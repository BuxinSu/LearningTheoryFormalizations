import MatrixConcentration.Prelude
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration

/-!
# Chapter 2: Matrix functions and probability with matrices

This merged chapter develops the matrix background used by the concentration
theory:

1. **Book §§2.1.4 and 2.1.7, §§2.1.13–2.1.17:** trace, Frobenius, entrywise,
   singular-value, and stable-rank tools;
2. **Book §§2.1.9–2.1.12:** standard matrix functions, power series, exponential,
   and logarithm;
3. **Book §2.1.16:** Hermitian dilation;
4. **Book §§2.2.2–2.2.5:** matrix-valued expectation, independence, order, and Jensen inequalities;
5. **Book §§2.2.6–2.2.9:** Hermitian and rectangular matrix variance.

The declarations below retain the original numeric order and documentation of
the ten Chapter 2 modules.  The shared definitions `IsSymmetricRV` and
`maxSummandSq` follow the probability portion so later chapters can use them
without depending on Chapter 1.
-/


set_option linter.unusedSectionVars false

/-!
# Trace identities and entrywise norms (Tropp §2.1.7, §2.1.4, §2.1.17)

* `trace_unitary_conj` — book eq. (2.1.7): the trace is
  unitarily invariant;
* trace of a Hermitian matrix = sum of its eigenvalues (§2.1.7): provided by
  `trace_eq_sum_eigenvalues_complex`/`trace_re_eq_sum_eigenvalues` (Prelude/Loewner);
* `frobeniusNorm` — book eq. (2.1.2) (§2.1.4), as a plain
  function (the scoped Mathlib Frobenius instance cannot coexist with the
  L2-operator-norm instance; `frobeniusNorm_eq_norm` is the Mathlib correspondence);
* `frobeniusNorm_replicateCol` — §2.1.4: "the Frobenius norm on 𝕄^{d×1} coincides
  with the ℓ₂ norm (2.1.1)";
* `trace_mul_conjTranspose_self`, `trace_conjTranspose_mul_self` — book eq. (2.1.8)
: `‖C‖_F² = tr(CC*) = tr(C*C)`;
* `entrywiseL1Norm` — book eq. **(2.1.30)**;
* `entrywiseL1Norm_le` — book eq. **(2.1.31)**:
  `‖B‖_{ℓ₁} ≤ √(d₁d₂)·‖B‖_F` "because of the Cauchy–Schwarz inequality".

The Schatten 1-norm (2.1.29) is deferred to the singular-value portion.
-/

namespace MatrixConcentration

open Matrix Finset

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Book eq. (2.1.7)** (§2.1.7): the trace is unitarily
invariant, `tr B = tr(QBQ*)`. Explicit (unnumbered) source statement. -/
theorem trace_unitary_conj (B : Matrix n n ℂ) {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : B.trace = (U * B * Uᴴ).trace := by
  have hUU : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    simpa [star_eq_conjTranspose] using h
  rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]

section Frobenius

/-- **Book eq. (2.1.2)** (§2.1.4): the Frobenius norm
`‖B‖_F = (Σᵢⱼ|bᵢⱼ|²)^{1/2}`, as a plain function. Explicit source declaration. -/
noncomputable def frobeniusNorm (B : Matrix m n ℂ) : ℝ :=
  √(∑ i, ∑ j, ‖B i j‖ ^ 2)

/-- Lean implementation helper: nonnegativity of the Frobenius norm. -/
lemma frobeniusNorm_nonneg (B : Matrix m n ℂ) : 0 ≤ frobeniusNorm B :=
  Real.sqrt_nonneg _

/-- Lean implementation helper: squaring the Frobenius norm removes its square root. -/
lemma frobeniusNorm_sq (B : Matrix m n ℂ) :
    frobeniusNorm B ^ 2 = ∑ i, ∑ j, ‖B i j‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Lean implementation helper: the Frobenius norm is conjugate-transpose
invariant. -/
lemma frobeniusNorm_conjTranspose (B : Matrix m n ℂ) :
    frobeniusNorm Bᴴ = frobeniusNorm B := by
  rw [frobeniusNorm, frobeniusNorm, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  show ‖(starRingEnd ℂ) (B i j)‖ = ‖B i j‖
  exact RCLike.norm_conj _

/-- **Book §2.1.4**: "the Frobenius norm on 𝕄^{d×1} coincides with the ℓ₂ norm (2.1.1)."
Implicit source claim. -/
lemma frobeniusNorm_replicateCol (x : m → ℂ) :
    frobeniusNorm (Matrix.replicateCol Unit x) = l2norm x := by
  rw [frobeniusNorm, l2norm_eq_sqrt_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.replicateCol_apply]

/-- **Book eq. (2.1.8)** (§2.1.7), first half:
`‖C‖_F² = tr(CC*)` — "This expression follows from the definitions (2.1.2) and (2.1.6)
and a short calculation." Explicit (unnumbered) source statement, reconstructed. -/
theorem trace_mul_conjTranspose_self (C : Matrix m n ℂ) :
    (C * Cᴴ).trace = ((frobeniusNorm C ^ 2 : ℝ) : ℂ) := by
  rw [frobeniusNorm_sq]
  show (∑ i, (C * Cᴴ) i i) = _
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : Cᴴ j i = (starRingEnd ℂ) (C i j) := rfl
  have h1 := RCLike.mul_conj (C i j)
  rw [h0, h1, ofReal_eq_complex]

/-- **Book eq. (2.1.8), second half**: `‖C‖_F² = tr(C*C)`. Explicit (unnumbered) source
statement. -/
theorem trace_conjTranspose_mul_self (C : Matrix m n ℂ) :
    (Cᴴ * C).trace = ((frobeniusNorm C ^ 2 : ℝ) : ℂ) := by
  have h1 := trace_mul_conjTranspose_self Cᴴ
  rw [Matrix.conjTranspose_conjTranspose, frobeniusNorm_conjTranspose] at h1
  exact h1

/-- **Book eq. (2.1.2).** Mathlib's scoped Frobenius norm. Mathlib correspondence
lemma (proved in an isolated section: the Frobenius and L2-operator scoped norm
instances must never be opened together). -/
lemma frobeniusNorm_eq_norm (B : Matrix m n ℂ) :
    frobeniusNorm B = @norm _ (Matrix.frobeniusSeminormedAddCommGroup).toNorm B := by
  rw [Matrix.frobenius_norm_def, frobeniusNorm, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Real.rpow_natCast ‖B i j‖ 2]
  norm_num

end Frobenius

section L1

/-- **Book eq. (2.1.30)** (§2.1.17): the entrywise ℓ₁ norm.
Implicit source declaration (quantity). -/
noncomputable def entrywiseL1Norm (B : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖B i j‖

/-- **Book eq. (2.1.31)** (§2.1.17):
`‖B‖_{ℓ₁} ≤ √(d₁d₂)·‖B‖_F` — "because of the Cauchy–Schwarz inequality."
Explicit (unnumbered) source statement. -/
theorem entrywiseL1Norm_le (B : Matrix m n ℂ) :
    entrywiseL1Norm B ≤
      Real.sqrt (Fintype.card m * Fintype.card n) * frobeniusNorm B := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (m × n))
    (fun _ => (1 : ℝ)) (fun p => ‖B p.1 p.2‖)
  simp only [one_mul, one_pow] at hcs
  have h1 : (∑ p : m × n, ‖B p.1 p.2‖) = entrywiseL1Norm B := by
    rw [entrywiseL1Norm, ← Finset.sum_product']
    rfl
  have h2 : (∑ _p : m × n, (1 : ℝ)) = (Fintype.card m * Fintype.card n : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod]
    ring
  have h3 : (∑ p : m × n, ‖B p.1 p.2‖ ^ 2) = frobeniusNorm B ^ 2 := by
    rw [frobeniusNorm_sq, ← Finset.sum_product']
    rfl
  rw [h1, h2, h3] at hcs
  have h4 : 0 ≤ entrywiseL1Norm B := by
    rw [← h1]
    positivity
  have h5 : (0 : ℝ) ≤ Fintype.card m * Fintype.card n := by positivity
  have h6 := Real.sqrt_le_sqrt hcs
  rw [Real.sqrt_sq h4, Real.sqrt_mul h5, Real.sqrt_sq (frobeniusNorm_nonneg B)] at h6
  exact h6

/-- **Book eq. (2.1.30), norm API:** the entrywise ℓ₁ quantity is subadditive.  This
is the triangle inequality implicit in the source's use of (2.1.30) as a matrix norm. -/
theorem entrywiseL1Norm_add_le (B C : Matrix m n ℂ) :
    entrywiseL1Norm (B + C) ≤ entrywiseL1Norm B + entrywiseL1Norm C := by
  simp only [entrywiseL1Norm, Matrix.add_apply]
  calc
    ∑ i, ∑ j, ‖B i j + C i j‖ ≤ ∑ i, ∑ j, (‖B i j‖ + ‖C i j‖) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_add_le _ _
    _ = (∑ i, ∑ j, ‖B i j‖) + ∑ i, ∑ j, ‖C i j‖ := by
      simp only [Finset.sum_add_distrib]

/-- **Book eq. (2.1.30), norm API:** complex homogeneity of the entrywise ℓ₁
quantity. -/
theorem entrywiseL1Norm_smul (a : ℂ) (B : Matrix m n ℂ) :
    entrywiseL1Norm (a • B) = ‖a‖ * entrywiseL1Norm B := by
  simp [entrywiseL1Norm, Finset.mul_sum]

/-- **Book eq. (2.1.30), norm API:** the entrywise ℓ₁ quantity separates
matrices. -/
theorem entrywiseL1Norm_eq_zero_iff (B : Matrix m n ℂ) :
    entrywiseL1Norm B = 0 ↔ B = 0 := by
  constructor
  · intro h
    ext i j
    have hi : ∑ j, ‖B i j‖ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => norm_nonneg _).mp h i (Finset.mem_univ i)
    have hij : ‖B i j‖ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => norm_nonneg _).mp hi j
        (Finset.mem_univ j)
    exact norm_eq_zero.mp hij
  · rintro rfl
    simp [entrywiseL1Norm]

/-- **Book eq. (2.1.30), bundled norm:** the entrywise ℓ₁ norm as a named
`AddGroupNorm`.  It is deliberately not installed as a global instance, because this
project also uses the Frobenius and L2-operator matrix norms. -/
noncomputable def entrywiseL1AddGroupNorm : AddGroupNorm (Matrix m n ℂ) where
  toFun := entrywiseL1Norm
  map_zero' := by simp [entrywiseL1Norm]
  add_le' := entrywiseL1Norm_add_le
  neg' := by simp [entrywiseL1Norm]
  eq_zero_of_map_eq_zero' := fun B => (entrywiseL1Norm_eq_zero_iff B).mp

/-- **Book eq. (2.1.30), bundled norm:** the named normed additive-group structure
induced by `entrywiseL1AddGroupNorm`; it is not a global instance. -/
@[reducible] noncomputable def entrywiseL1NormedAddCommGroup :
    NormedAddCommGroup (Matrix m n ℂ) :=
  entrywiseL1AddGroupNorm.toNormedAddCommGroup

/-- **Book eq. (2.1.30), value correspondence:** the norm of the named entrywise-ℓ₁
structure is exactly `entrywiseL1Norm`. -/
theorem entrywiseL1Norm_eq_bundled_norm (B : Matrix m n ℂ) :
    entrywiseL1Norm B =
      @norm (Matrix m n ℂ) entrywiseL1NormedAddCommGroup.toNorm B :=
  rfl

end L1

end MatrixConcentration


set_option linter.unusedSectionVars false

/-!
# Standard matrix functions (Tropp §2.1.9–§2.1.10)

**Definition 2.1.2 (Standard Matrix Function)** of the book defines `f(A)`, for
`f : I → ℝ` on an interval containing the eigenvalues of a Hermitian `A`, by applying
`f` to the eigenvalues in an eigenvalue decomposition `A = Q Λ Q*`. In this
formalization `f(A)` is realized as Mathlib's continuous functional calculus `cfc f A`
(every `f : ℝ → ℝ` is continuous on the finite spectrum of a matrix, so `cfc` carries
no continuity restriction here); `cfc_eq_book_formula` shows that `cfc f A` is
*literally* the book's triple product for the canonical eigendecomposition, and
`cfc_unitary_diagonal` discharges the book's hidden well-definedness obligation
("It can be verified that the definition of `f(A)` does not depend on which eigenvalue
decomposition that we choose"): *every* unitary real-diagonalization computes the same
matrix.

* `cfc_eq_book_formula` — Definition 2.1.2 (Mathlib correspondence);
* `cfc_unitary_diagonal` — well-definedness of Definition 2.1.2 (implicit obligation);
* `cfc_diagonal_real` — "we can apply `f` to a real diagonal matrix by applying the
  function to each diagonal entry" (Def. 2.1.2);
* `cfc_pow_eq` — "the power function `f(A) = A^q`" (p. 22);
* `eigenvalues_cfc_multiset`, `spectral_mapping` — **Proposition 2.1.3 (Spectral
  Mapping Theorem)**, stated by the source without proof ("immediate");
* `transfer_rule` — **Proposition 2.1.4 (Transfer Rule)**, following the source's
  proof (diagonal case + Conjugation Rule);
* `lambdaMax_cfc_of_monotone` — the interface fact `λ_max(f(A)) = f(λ_max(A))` for
  monotone `f`, forced by later use (Chapter 3, e.g. line "the Spectral Mapping
  Theorem … and the fact that the exponential function is increasing").
-/

namespace MatrixConcentration

open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℂ}

/-- Lean implementation helper: standard matrix functions of Hermitian matrices are
Hermitian (the codomain assertion `f(A) ∈ ℍ_d` of Definition 2.1.2). -/
lemma isHermitian_cfc (f : ℝ → ℝ) (A : Matrix n n ℂ) : (cfc f A).IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate f A)

/-- **Book Definition 2.1.2 (Standard Matrix Function)**, §2.1.9. Mathlib correspondence
lemma: `cfc f A` is exactly the book's `Q · diag(f(λ₁),…,f(λ_d)) · Q*` for the canonical
eigendecomposition. -/
theorem cfc_eq_book_formula (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

section WellDefined

/-- Lean implementation helper (intertwining): if `A = U diag(d) U*` and
`A = V diag(λ) V*`, then `W := V* U` intertwines the two diagonals, and therefore
intertwines `g(d)` and `g(λ)` for *every* function `g`. This is the engine behind the
well-definedness of Definition 2.1.2. -/
private lemma intertwine_of_eq {U V : Matrix n n ℂ} (hUmem : U ∈ Matrix.unitaryGroup n ℂ)
    (hVmem : V ∈ Matrix.unitaryGroup n ℂ) {d lam : n → ℝ}
    (heq : V * diagonal (RCLike.ofReal ∘ lam) * Vᴴ = U * diagonal (RCLike.ofReal ∘ d) * Uᴴ)
    (g : ℝ → ℝ) :
    diagonal (RCLike.ofReal ∘ g ∘ lam) * (Vᴴ * U) =
      (Vᴴ * U) * diagonal (RCLike.ofReal ∘ g ∘ d) := by
  have hVV : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hVmem
    simpa [star_eq_conjTranspose] using h
  have hUU : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hUmem
    simpa [star_eq_conjTranspose] using h
  have hmat : diagonal (RCLike.ofReal ∘ lam) * (Vᴴ * U) =
      (Vᴴ * U) * diagonal (RCLike.ofReal ∘ d) := by
    have h1 : Vᴴ * (V * diagonal (RCLike.ofReal ∘ lam) * Vᴴ) * U =
        Vᴴ * (U * diagonal (RCLike.ofReal ∘ d) * Uᴴ) * U := by rw [heq]
    have hL : Vᴴ * (V * diagonal (RCLike.ofReal ∘ lam) * Vᴴ) * U =
        diagonal (RCLike.ofReal ∘ lam) * (Vᴴ * U) := by
      simp only [← Matrix.mul_assoc]
      rw [hVV, Matrix.one_mul]
    have hR : Vᴴ * (U * diagonal (RCLike.ofReal ∘ d) * Uᴴ) * U =
        (Vᴴ * U) * diagonal (RCLike.ofReal ∘ d) := by
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (Vᴴ * U * diagonal (RCLike.ofReal ∘ d)) Uᴴ U, hUU,
        Matrix.mul_one]
    rw [← hL, h1, hR]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hentry : (RCLike.ofReal ∘ lam) i * (Vᴴ * U) i j =
      (Vᴴ * U) i j * (RCLike.ofReal ∘ d) j := by
    rw [← Matrix.ext_iff] at hmat
    have h2 := hmat i j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at h2
  simp only [Function.comp_apply, ofReal_eq_complex] at hentry ⊢
  by_cases hw : (Vᴴ * U) i j = 0
  · simp [hw]
  · have hld' : lam i = d j := by
      have h1 : (lam i : ℂ) * (Vᴴ * U) i j = (d j : ℂ) * (Vᴴ * U) i j := by
        rw [hentry]
        ring
      exact_mod_cast mul_right_cancel₀ hw h1
    rw [hld']
    ring

/-- **Book Definition 2.1.2, well-definedness** (§2.1.9, p. 21: "It can be verified
that the definition of `f(A)` does not depend on which eigenvalue decomposition
`A = QΛQ*` that we choose"). Implicit source declaration (hidden proof obligation):
every unitary real-diagonalization of `A` computes the standard matrix function. -/
theorem cfc_unitary_diagonal (hA : A.IsHermitian) {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) {d : n → ℝ}
    (hAeq : A = U * diagonal (RCLike.ofReal ∘ d) * Uᴴ) (f : ℝ → ℝ) :
    cfc f A = U * diagonal (RCLike.ofReal ∘ f ∘ d) * Uᴴ := by
  have hVmem : (hA.eigenvectorUnitary : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ :=
    hA.eigenvectorUnitary.2
  have heq : (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ =
      U * diagonal (RCLike.ofReal ∘ d) * Uᴴ :=
    (spectral_decomposition hA).symm.trans hAeq
  have hint := intertwine_of_eq hU hVmem heq f
  have hVV' : (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hVmem
    simpa [star_eq_conjTranspose] using h
  have hUU' : U * Uᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hU
    simpa [star_eq_conjTranspose] using h
  rw [cfc_eq_book_formula hA f]
  have h3 : (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) *
        ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * U)) * Uᴴ =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * U) *
        diagonal (RCLike.ofReal ∘ f ∘ d)) * Uᴴ := by rw [hint]
  have hL : (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) *
        ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * U)) * Uᴴ =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc _ U Uᴴ, hUU', Matrix.mul_one]
  have hR : (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * U) *
        diagonal (RCLike.ofReal ∘ f ∘ d)) * Uᴴ =
      U * diagonal (RCLike.ofReal ∘ f ∘ d) * Uᴴ := by
    simp only [← Matrix.mul_assoc]
    rw [hVV', Matrix.one_mul]
  rw [← hL, h3, hR]

end WellDefined

/-- Lean implementation helper: a real diagonal matrix is Hermitian. -/
lemma isHermitian_diagonal_ofReal (d : n → ℝ) :
    (diagonal (RCLike.ofReal ∘ d) : Matrix n n ℂ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp [Pi.star_apply, RCLike.star_def, ofReal_eq_complex]

/-- **Book Definition 2.1.2, final clause**: "we can apply `f` to a real diagonal matrix by
applying the function to each diagonal entry." Explicit source declaration. -/
theorem cfc_diagonal_real (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (RCLike.ofReal ∘ d) : Matrix n n ℂ) =
      diagonal (RCLike.ofReal ∘ f ∘ d) := by
  have h1 : (diagonal (RCLike.ofReal ∘ d) : Matrix n n ℂ) =
      (1 : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ d) * (1 : Matrix n n ℂ)ᴴ := by
    rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  have h2 := cfc_unitary_diagonal (isHermitian_diagonal_ofReal d)
    (Submonoid.one_mem _) h1 f
  rwa [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] at h2

/-- **Book §2.1.9, p. 22**: "consider the power function f(t) = t^q … the power function
`f(A) = A^q`, where `A^q` is the q-fold product of `A`." Implicit source declaration
(consistency of Definition 2.1.2 with matrix powers); Mathlib correspondence
(`cfc_pow_id`). -/
theorem cfc_pow_eq (hA : A.IsHermitian) (q : ℕ) :
    cfc (fun x : ℝ => x ^ q) A = A ^ q :=
  cfc_pow_id A q hA.isSelfAdjoint

/-- **Book Proposition 2.1.3 (Spectral Mapping Theorem)**, sharp multiset form: the
eigenvalue list of `f(A)` is the image under `f` of the eigenvalue list of `A`.
Implicit source declaration (the book's statement, plus the multiplicity information
forced by later use). -/
theorem eigenvalues_cfc_multiset (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Multiset.map ((isHermitian_cfc f A).eigenvalues) Finset.univ.val =
      Multiset.map (f ∘ hA.eigenvalues) Finset.univ.val :=
  (eigenvalues_multiset_unique (isHermitian_cfc f A) hA.eigenvectorUnitary.2
    (cfc_eq_book_formula hA f)).symm

/-- **Book Proposition 2.1.3 (Spectral Mapping Theorem)**, §2.1.9: "If λ is an
eigenvalue of A, then f(λ) is an eigenvalue of f(A)." Explicit source declaration;
the source gives no proof ("an immediate, but important, consequence"). -/
theorem spectral_mapping (hA : A.IsHermitian) (f : ℝ → ℝ) (i : n) :
    ∃ j, (isHermitian_cfc f A).eigenvalues j = f (hA.eigenvalues i) := by
  have h1 : f (hA.eigenvalues i) ∈
      Multiset.map ((isHermitian_cfc f A).eigenvalues) Finset.univ.val := by
    rw [eigenvalues_cfc_multiset hA f]
    exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp h1
  exact ⟨j, hj⟩

/-- **Book Proposition 2.1.4 (Transfer Rule)**, §2.1.10, eq. (2.1.14): if `f ≤ g` on an
interval `I` containing the eigenvalues of `A`, then `f(A) ≼ g(A)`. Explicit source
declaration; the source's proof (diagonal comparison + Conjugation Rule) is followed.

Author note: Lean proves the transfer rule for an arbitrary spectral set `I`, not only
an interval. -/
theorem transfer_rule (hA : A.IsHermitian) {I : Set ℝ} (hspec : ∀ i, hA.eigenvalues i ∈ I)
    {f g : ℝ → ℝ} (hfg : ∀ a ∈ I, f a ≤ g a) : cfc f A ≤ cfc g A := by
  rw [Matrix.le_iff]
  have h1 : cfc g A - cfc f A =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ (fun x => g x - f x) ∘ hA.eigenvalues) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    rw [cfc_eq_book_formula hA f, cfc_eq_book_formula hA g, ← Matrix.sub_mul,
      ← Matrix.mul_sub]
    congr 2
    ext i j
    rw [Matrix.sub_apply]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Function.comp_apply, ofReal_eq_complex]
      push_cast
      ring
    · simp only [Matrix.diagonal_apply_ne _ hij, sub_zero]
  rw [h1]
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ _
  exact (posSemidef_diagonal_real_iff _).mpr fun i => by
    have := hfg (hA.eigenvalues i) (hspec i)
    simp only [Function.comp_apply]
    linarith

section MonotoneInterface

/-- Lean implementation helper: interface fact forced by Chapter 3 (a source prerequisite
recovered from context;
used at "The first identity depends on the Spectral Mapping Theorem … and the fact
that the exponential function is increasing"): for monotone `f`,
`λ_max(f(A)) = f(λ_max(A))`. -/
theorem lambdaMax_cfc_of_monotone [Nonempty n] (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : Monotone f) : lambdaMax (isHermitian_cfc f A) = f (lambdaMax hA) := by
  have hmulti := eigenvalues_cfc_multiset hA f
  refine le_antisymm ?_ ?_
  · refine lambdaMax_le _ fun j => ?_
    have hj : (isHermitian_cfc f A).eigenvalues j ∈
        Multiset.map (f ∘ hA.eigenvalues) Finset.univ.val := by
      rw [← hmulti]
      exact Multiset.mem_map.mpr ⟨j, Finset.mem_univ_val j, rfl⟩
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hj
    rw [← hi]
    exact hf (eigenvalues_le_lambdaMax hA i)
  · obtain ⟨i, hi⟩ := exists_eigenvalues_eq_lambdaMax hA
    obtain ⟨j, hj⟩ := spectral_mapping hA f i
    rw [← hi, ← hj]
    exact eigenvalues_le_lambdaMax _ j

/-- Lean implementation helper: the `λ_min` companion interface fact. -/
theorem lambdaMin_cfc_of_monotone [Nonempty n] (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : Monotone f) : lambdaMin (isHermitian_cfc f A) = f (lambdaMin hA) := by
  have hmulti := eigenvalues_cfc_multiset hA f
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi⟩ := exists_eigenvalues_eq_lambdaMin hA
    obtain ⟨j, hj⟩ := spectral_mapping hA f i
    rw [← hi, ← hj]
    exact lambdaMin_le_eigenvalues _ j
  · refine le_lambdaMin _ fun j => ?_
    have hj : (isHermitian_cfc f A).eigenvalues j ∈
        Multiset.map (f ∘ hA.eigenvalues) Finset.univ.val := by
      rw [← hmulti]
      exact Multiset.mem_map.mpr ⟨j, Finset.mem_univ_val j, rfl⟩
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hj
    rw [← hi]
    exact hf (lambdaMin_le_eigenvalues hA i)

end MonotoneInterface

end MatrixConcentration


set_option linter.unusedSectionVars false

/-!
# Power-series representation of standard matrix functions (Tropp §2.1.9, p. 22)

The book's display: "When a real function has a power series expansion, we can also
represent the standard matrix function with the same power series expansion. …
`f(a) = c₀ + Σ_{q≥1} c_q a^q` for `a ∈ I` implies `f(A) = c₀I + Σ_{q≥1} c_q A^q`.
This formula can be verified using an eigenvalue decomposition of `A` and the
definition of a standard matrix function" — which is exactly the proof given here:
the partial sums of the matrix series are the standard matrix functions of the scalar
partial sums (`diagMap`, linearity), and convergence passes through the (continuous)
conjugation-by-eigenvectors map. Convergence of matrices is entrywise, i.e. in the
product topology (per §2.1.4, all norms induce the same convergence).
-/

namespace MatrixConcentration

open Matrix Finset Filter

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℂ}

section DiagMap

variable (hA : A.IsHermitian)

/-- Lean implementation helper: the "eigendecomposition transport" map
`d ↦ Q · diag(d) · Q*`, as an `ℝ`-linear map. -/
noncomputable def diagMap (hA : A.IsHermitian) : (n → ℝ) →ₗ[ℝ] Matrix n n ℂ where
  toFun d := (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ d) *
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ
  map_add' d₁ d₂ := by
    have h1 : diagonal (RCLike.ofReal ∘ (d₁ + d₂)) =
        diagonal ((RCLike.ofReal ∘ d₁ : n → ℂ)) + diagonal (RCLike.ofReal ∘ d₂) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Function.comp_apply,
          Pi.add_apply, ofReal_eq_complex]
        push_cast
        ring
      · simp [Matrix.diagonal_apply_ne _ hij]
    rw [h1, Matrix.mul_add, Matrix.add_mul]
  map_smul' r d := by
    have h1 : diagonal (RCLike.ofReal ∘ (r • d)) =
        (r : ℂ) • diagonal ((RCLike.ofReal ∘ d : n → ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, Function.comp_apply,
          Pi.smul_apply, smul_eq_mul, ofReal_eq_complex]
        push_cast
        ring
      · simp [Matrix.diagonal_apply_ne _ hij]
    rw [h1, Matrix.mul_smul, Matrix.smul_mul]
    have h2 : ∀ M : Matrix n n ℂ, (r : ℂ) • M = r • M := fun M => by
      ext i j
      show (r : ℂ) * M i j = r • M i j
      rw [Complex.real_smul]
    rw [h2]
    rfl

/-- Lean implementation helper: unfolding the diagonal functional-calculus map. -/
lemma diagMap_apply (d : n → ℝ) :
    diagMap hA d = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (RCLike.ofReal ∘ d) * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := rfl

/-- Lean implementation helper: `diagMap` at the constant function `1` is the
identity matrix. -/
lemma diagMap_one : diagMap hA (fun _ => 1) = 1 := by
  have h2 : (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
    simpa [star_eq_conjTranspose] using h
  rw [diagMap_apply]
  have h1 : diagonal (RCLike.ofReal ∘ (fun _ : n => (1 : ℝ))) = (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply_eq, ofReal_eq_complex]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [h1, Matrix.mul_one, h2]

/-- Lean implementation helper: `diagMap` at the `q`-th powers of the eigenvalues is
`A^q` (Definition 2.1.2's consistency with powers, `cfc_pow_eq`). -/
lemma diagMap_pow (q : ℕ) : diagMap hA (fun i => hA.eigenvalues i ^ q) = A ^ q := by
  have h1 := cfc_eq_book_formula hA (fun x : ℝ => x ^ q)
  have h2 := cfc_pow_eq hA q
  rw [diagMap_apply]
  rw [← h2, h1]
  rfl

/-- Lean implementation helper: `diagMap` at `f ∘ eigenvalues` is the standard matrix
function `f(A)`. -/
lemma diagMap_comp_eigenvalues (f : ℝ → ℝ) :
    diagMap hA (fun i => f (hA.eigenvalues i)) = cfc f A := by
  rw [cfc_eq_book_formula hA f, diagMap_apply]
  rfl

/-- Lean implementation helper: `diagMap` is continuous (in the product topology). -/
lemma continuous_diagMap : Continuous (diagMap hA) := by
  have hVcont : Continuous fun X : Matrix n n ℂ =>
      (hA.eigenvectorUnitary : Matrix n n ℂ) * X *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have h1 : (fun X : Matrix n n ℂ => ((hA.eigenvectorUnitary : Matrix n n ℂ) * X *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ) i j) =
        fun X => ∑ a, (∑ b, (hA.eigenvectorUnitary : Matrix n n ℂ) i b * X b a) *
          (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ a j := by
      funext X
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [Matrix.mul_apply]
    rw [h1]
    refine continuous_finsetSum _ fun a _ => Continuous.mul ?_ continuous_const
    exact continuous_finsetSum _ fun b _ =>
      Continuous.mul continuous_const ((continuous_apply a).comp (continuous_apply b))
  have hdiagcont : Continuous fun d : n → ℝ =>
      (diagonal (RCLike.ofReal ∘ d) : Matrix n n ℂ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    by_cases hij : i = j
    · subst hij
      have h2 : (fun d : n → ℝ => (diagonal (RCLike.ofReal ∘ d) : Matrix n n ℂ) i i) =
          fun d => ((d i : ℝ) : ℂ) := by
        funext d
        rw [Matrix.diagonal_apply_eq]
        exact ofReal_eq_complex _
      rw [h2]
      exact Complex.continuous_ofReal.comp (continuous_apply i)
    · have h2 : (fun d : n → ℝ => (diagonal (RCLike.ofReal ∘ d) : Matrix n n ℂ) i j) =
          fun _ => 0 := by
        funext d
        exact Matrix.diagonal_apply_ne _ hij
      rw [h2]
      exact continuous_const
  exact hVcont.comp hdiagcont

end DiagMap

/-- **Book §2.1.9, p. 22 (power-series display)**: "`f(a) = c₀ + Σ_{q≥1} c_q a^q` for
`a ∈ I` implies `f(A) = c₀ I + Σ_{q≥1} c_q A^q`" — if the scalar power series converges
to `f` at every point of an interval containing the eigenvalues of `A`, then the
matrix power series converges (entrywise) to the standard matrix function `f(A)`.
Explicit (unnumbered) source statement; the source sketches the proof ("can be
verified using an eigenvalue decomposition"), which is the proof given here. -/
theorem matrixFun_powerSeries (hA : A.IsHermitian) {I : Set ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ I) {c : ℕ → ℝ} {f : ℝ → ℝ}
    (hf : ∀ a ∈ I, Filter.Tendsto
      (fun N => c 0 + ∑ q ∈ Finset.Icc 1 N, c q * a ^ q) Filter.atTop (nhds (f a))) :
    Filter.Tendsto
      (fun N => (c 0 : ℂ) • (1 : Matrix n n ℂ) + ∑ q ∈ Finset.Icc 1 N, (c q : ℂ) • A ^ q)
      Filter.atTop (nhds (cfc f A)) := by
  -- the scalar partial sums, transported through `diagMap`
  have hseq : Filter.Tendsto
      (fun N => fun i => c 0 + ∑ q ∈ Finset.Icc 1 N, c q * hA.eigenvalues i ^ q)
      Filter.atTop (nhds fun i => f (hA.eigenvalues i)) := by
    rw [tendsto_pi_nhds]
    intro i
    exact hf (hA.eigenvalues i) (hspec i)
  have hcomp := ((continuous_diagMap hA).tendsto _).comp hseq
  rw [diagMap_comp_eigenvalues hA f] at hcomp
  -- identify the transported partial sums with the matrix partial sums
  have hpartial : ∀ N, diagMap hA
      (fun i => c 0 + ∑ q ∈ Finset.Icc 1 N, c q * hA.eigenvalues i ^ q) =
      (c 0 : ℂ) • (1 : Matrix n n ℂ) + ∑ q ∈ Finset.Icc 1 N, (c q : ℂ) • A ^ q := by
    intro N
    have hdecomp : (fun i => c 0 + ∑ q ∈ Finset.Icc 1 N, c q * hA.eigenvalues i ^ q) =
        c 0 • (fun _ : n => (1 : ℝ)) +
          ∑ q ∈ Finset.Icc 1 N, c q • (fun i => hA.eigenvalues i ^ q) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, Finset.sum_apply]
    have hcast : ∀ (r : ℝ) (M : Matrix n n ℂ), r • M = (r : ℂ) • M := fun r M => by
      ext i j
      show r • M i j = (r : ℂ) * M i j
      rw [Complex.real_smul]
    rw [hdecomp, map_add, map_smul, map_sum, diagMap_one, hcast]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, diagMap_pow hA q, hcast]
  have hfinal : (fun N => diagMap hA
      (fun i => c 0 + ∑ q ∈ Finset.Icc 1 N, c q * hA.eigenvalues i ^ q)) =
      fun N => (c 0 : ℂ) • (1 : Matrix n n ℂ) +
        ∑ q ∈ Finset.Icc 1 N, (c q : ℂ) • A ^ q :=
    funext hpartial
  rwa [show ((diagMap hA) ∘ fun N =>
      (fun i => c 0 + ∑ q ∈ Finset.Icc 1 N, c q * hA.eigenvalues i ^ q)) =
      fun N => (c 0 : ℂ) • (1 : Matrix n n ℂ) +
        ∑ q ∈ Finset.Icc 1 N, (c q : ℂ) • A ^ q from hfinal] at hcomp

end MatrixConcentration


set_option linter.unusedSectionVars false

/-!
# The matrix exponential and logarithm (Tropp §2.1.11–§2.1.12)

* `matrixExp_eq_cfc` — book eq. (2.1.15): the matrix exponential as a
  standard matrix function coincides with the power-series exponential
  (`NormedSpace.exp` is *defined* by the series (2.1.15), see `NormedSpace.exp_eq_tsum`;
  Mathlib correspondence `CFC.real_exp_eq_normedSpace_exp`);
* `posDef_exp` — §2.1.11: "the exponential of an Hermitian matrix is always positive
  definite" (via the Spectral Mapping Theorem, as the source indicates);
* `trace_exp_monotone` — **book eq. (2.1.16)**: `A ≼ H` implies
  `tr e^A ≤ tr e^H`. The source defers the proof to §8.4.4 (Courant–Fischer/Weyl route).
  Courant–Fischer is not yet available in Mathlib, so we give an **alternative complete
  proof** (Peierls–Bogoliubov): comparing diagonal entries in the eigenbasis of `A` and
  applying the finite Jensen inequality for `exp`; see the proof audit for the
  equivalence discussion;
* `log_exp_eq` — book eq. (2.1.17): `log(e^A) = A`;
* `log_monotone` — **book eq. (2.1.18)**: for positive-definite
  `A ≼ H`, `log A ≼ log H`. The source defers the proof to §8.4.6; here it is obtained
  from Mathlib's `CFC.log_le_log` (equivalent Mathlib proof via the Löwner integral
  representation, the same circle of ideas as the book's Chapter 8 argument).

The matrix logarithm of the book (§2.1.12, standard matrix function of `Real.log` on
positive-definite matrices) is `CFC.log`, which is *by definition* `cfc Real.log`.
-/

namespace MatrixConcentration

open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A H : Matrix n n ℂ}

/-- **Book eq. (2.1.15) (§2.1.11)**: the standard-matrix-function
exponential (Definition 2.1.2 applied to `exp`) equals the power-series matrix
exponential. Mathlib correspondence lemma (`NormedSpace.exp` is defined by the series
`∑ Aᵠ/q!`). -/
theorem matrixExp_eq_cfc (hA : A.IsHermitian) :
    NormedSpace.exp A = cfc Real.exp A :=
  (CFC.real_exp_eq_normedSpace_exp (Matrix.isHermitian_iff_isSelfAdjoint.mp hA)).symm

/-- Lean implementation helper: the matrix exponential of a Hermitian matrix is
Hermitian. -/
lemma isHermitian_exp (hA : A.IsHermitian) : (NormedSpace.exp A).IsHermitian := by
  rw [matrixExp_eq_cfc hA]
  exact isHermitian_cfc Real.exp A

/-- **Book §2.1.11, p. 22**: "the exponential of an Hermitian matrix is always positive
definite" (via the Spectral Mapping Theorem, Proposition 2.1.3, as the source
indicates). Implicit source declaration. -/
theorem posDef_exp (hA : A.IsHermitian) : (NormedSpace.exp A).PosDef := by
  rw [matrixExp_eq_cfc hA]
  refine posDef_iff_exists_eigenvalues_pos.mpr ⟨isHermitian_cfc Real.exp A, fun j => ?_⟩
  have hj : (isHermitian_cfc Real.exp A).eigenvalues j ∈
      Multiset.map (Real.exp ∘ hA.eigenvalues) Finset.univ.val := by
    rw [← eigenvalues_cfc_multiset hA Real.exp]
    exact Multiset.mem_map.mpr ⟨j, Finset.mem_univ_val j, rfl⟩
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hj
  rw [← hi]
  exact Real.exp_pos _

/-- Lean implementation helper: the trace of the matrix exponential in eigenvalue
coordinates. -/
lemma trace_exp_re_eq_sum (hA : A.IsHermitian) :
    ((NormedSpace.exp A).trace).re = ∑ i, Real.exp (hA.eigenvalues i) := by
  rw [matrixExp_eq_cfc hA, trace_cfc_eq_sum hA Real.exp]
  exact Complex.ofReal_re _

/-- Lean implementation helper: monotonicity of the Rayleigh value in the Loewner
order. -/
lemma rayleigh_mono_of_loewner_le (hle : A ≤ H) (u : n → ℂ) :
    rayleigh A u ≤ rayleigh H u := by
  have h2 : (0 : ℝ) ≤ rayleigh (H - A) u :=
    (Matrix.le_iff.mp hle).re_dotProduct_nonneg u
  rw [rayleigh_sub] at h2
  linarith

/-- Lean implementation helper: Peierls–Bogoliubov pointwise inequality recovered from
context, engine of the alternative proof of (2.1.16)): for a unit vector `u` and
Hermitian `H`, `exp(u*Hu) ≤ u*(e^H)u`. Proof: expand both sides in the eigenbasis of
`H` and apply the finite Jensen inequality for the convex function `exp`. -/
lemma exp_rayleigh_le_dotProduct_exp (hH : H.IsHermitian) {u : n → ℂ}
    (hu : l2norm u = 1) :
    Real.exp (rayleigh H u) ≤ (star u ⬝ᵥ (NormedSpace.exp H *ᵥ u)).re := by
  have h2 : star u ⬝ᵥ (NormedSpace.exp H *ᵥ u) =
      ((∑ j, (Real.exp ∘ hH.eigenvalues) j *
        ‖((hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ u) j‖ ^ 2 : ℝ) : ℂ) := by
    rw [matrixExp_eq_cfc hH]
    exact star_dotProduct_mulVec_eq_sum hH.eigenvectorUnitary.2
      (cfc_eq_book_formula hH Real.exp) u
  rw [h2, Complex.ofReal_re, rayleigh_eq_sum hH u]
  have hsum : ∑ j, ‖((hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ u) j‖ ^ 2 = 1 := by
    rw [sum_norm_sq_conjTranspose_mulVec hH.eigenvectorUnitary.2 u, hu, one_pow]
  have hjensen := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := fun j => ‖((hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ u) j‖ ^ 2)
    (p := fun j => hH.eigenvalues j)
    (fun j _ => by positivity) hsum (fun j _ => Set.mem_univ _)
  calc Real.exp (∑ j, hH.eigenvalues j *
        ‖((hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ u) j‖ ^ 2)
      = Real.exp (∑ j, ‖((hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ u) j‖ ^ 2 •
          hH.eigenvalues j) := by
        congr 1
        exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul]; ring
    _ ≤ ∑ j, ‖((hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ u) j‖ ^ 2 *
          Real.exp (hH.eigenvalues j) := hjensen
    _ = ∑ j, (Real.exp ∘ hH.eigenvalues) j *
          ‖((hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ u) j‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [Function.comp_apply]; ring

/-- Lean implementation helper: the trace of a conjugated matrix as a sum of quadratic
forms over the columns of `V`. -/
lemma trace_conj_eq_sum_dotProduct (M V : Matrix n n ℂ) :
    (Vᴴ * M * V).trace = ∑ i, star (fun j => V j i) ⬝ᵥ (M *ᵥ fun j => V j i) := by
  have hterm : ∀ i, star (fun j => V j i) ⬝ᵥ (M *ᵥ fun j => V j i) =
      ∑ j, ∑ k, star (V j i) * (M j k * V k i) := fun i => by
    show (∑ j, star (V j i) * ∑ k, M j k * V k i) = _
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  have htr : (Vᴴ * M * V).trace = ∑ i, ∑ k, ∑ j, star (V j i) * (M j k * V k i) := by
    show (∑ i, (Vᴴ * M * V) i i) = _
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.conjTranspose_apply]; ring
  rw [htr]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hterm i, Finset.sum_comm]

/-- **Book eq. (2.1.16)** (§2.1.11): the trace exponential is
monotone with respect to the semidefinite order: `A ≼ H ⟹ tr e^A ≤ tr e^H`.

Explicit (unnumbered) source statement; the source establishes it in §8.4.4 via the
Courant–Fischer theorem. Alternative complete proof here (Peierls–Bogoliubov):
`tr e^A = ∑ᵢ exp(uᵢ*Auᵢ) ≤ ∑ᵢ exp(uᵢ*Huᵢ) ≤ ∑ᵢ uᵢ*(e^H)uᵢ = tr e^H`, where `{uᵢ}` is
the eigenbasis of `A`; the middle step is `A ≼ H`, the last is Jensen's inequality for
`exp` in the eigenbasis of `H`, and the final identity is unitary invariance of the
trace. -/
theorem trace_exp_monotone (hA : A.IsHermitian) (hH : H.IsHermitian) (hle : A ≤ H) :
    ((NormedSpace.exp A).trace).re ≤ ((NormedSpace.exp H).trace).re := by
  have hVV' : (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
    simpa [star_eq_conjTranspose] using h
  have hcycle : (NormedSpace.exp H).trace =
      ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * NormedSpace.exp H *
        (hA.eigenvectorUnitary : Matrix n n ℂ)).trace := by
    rw [Matrix.trace_mul_cycle, hVV', Matrix.one_mul]
  rw [trace_exp_re_eq_sum hA, hcycle, trace_conj_eq_sum_dotProduct, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hcol : (fun j => (hA.eigenvectorUnitary : Matrix n n ℂ) j i) =
      ⇑(hA.eigenvectorBasis i) :=
    funext fun j => hA.eigenvectorUnitary_apply j i
  rw [hcol]
  have hu : l2norm (⇑(hA.eigenvectorBasis i)) = 1 := l2norm_eigenvectorBasis hA i
  calc Real.exp (hA.eigenvalues i)
      = Real.exp (rayleigh A (⇑(hA.eigenvectorBasis i))) := by
        rw [rayleigh_eigenvectorBasis]
    _ ≤ Real.exp (rayleigh H (⇑(hA.eigenvectorBasis i))) :=
        Real.exp_le_exp.mpr (rayleigh_mono_of_loewner_le hle _)
    _ ≤ (star ⇑(hA.eigenvectorBasis i) ⬝ᵥ
          (NormedSpace.exp H *ᵥ ⇑(hA.eigenvectorBasis i))).re :=
        exp_rayleigh_le_dotProduct_exp hH hu

section Log

/-- Lean implementation helper: with the L2 operator norm, square complex matrices form
a C⋆-algebra. Assembled from Mathlib's scoped `Matrix.Norms.L2Operator` instances (no
global instance exists in Mathlib because the matrix norm is a scoped choice). -/
noncomputable scoped instance instCStarAlgebraMatrix : CStarAlgebra (Matrix n n ℂ) where

/-- **Book §2.1.12**: the matrix logarithm as a standard matrix function. `CFC.log` is by
definition `cfc Real.log`; this restates it in the book's Definition-2.1.2 shape.
Mathlib correspondence lemma. -/
theorem log_eq_book_formula (hA : A.IsHermitian) :
    CFC.log A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (RCLike.ofReal ∘ Real.log ∘ hA.eigenvalues) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  unfold CFC.log
  exact cfc_eq_book_formula hA Real.log

/-- **Book eq. (2.1.17) (§2.1.12)**: "The matrix logarithm is also the
functional inverse of the matrix exponential: `log(e^A) = A` for each Hermitian `A`."
Explicit (unnumbered) source statement; Mathlib correspondence (`CFC.log_exp`). -/
theorem log_exp_eq (hA : A.IsHermitian) : CFC.log (NormedSpace.exp A) = A :=
  CFC.log_exp A (Matrix.isHermitian_iff_isSelfAdjoint.mp hA)

/-- **Book eq. (2.1.18)** (§2.1.12): the matrix logarithm preserves
the semidefinite order: for positive-definite `A ≼ H`, `log A ≼ log H`.

Explicit (unnumbered) source statement; the source establishes it in §8.4.6 (via the
integral representation of the logarithm and the operator anti-monotonicity of the
inverse). Here obtained from Mathlib's `CFC.log_le_log`, whose proof follows the same
Löwner integral-representation strategy — an equivalent Mathlib proof. -/
theorem log_monotone (hA : A.PosDef) (_hH : H.PosDef) (hle : A ≤ H) :
    CFC.log A ≤ CFC.log H :=
  CFC.log_le_log hle hA.isStrictlyPositive

end Log

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Singular values, the spectral norm, and the stable rank (Tropp §2.1.13–§2.1.15, §2.1.17)

* `singularValues` — the singular values of a rectangular matrix `B`, realized as
  `√(eigenvalues of B*B)` (book §2.1.13, C2-47); `singularValues_sq_multiset_eq` is the
  decomposition-independence (well-definedness) statement;
* `exists_svd` — **book eq. (2.1.19)** (C2-46):
  every `d₁ × d₂` matrix admits an SVD `B = UΣW*` with `U`, `W` unitary and `Σ` a
  rectangular nonnegative "diagonal" whose diagonal entries are the singular values in
  weakly decreasing order.  The source states this without proof; the proof below is the
  standard construction the source alludes to on p. 24 ("Conversely, we can always
  extract...", C2-50): diagonalize `B*B`, normalize the images of the eigenvectors with
  nonzero eigenvalue, and extend to an orthonormal basis;
* `svd_mul_conjTranspose`, `svd_conjTranspose_mul` — **book eq. (2.1.20)**
 (C2-48); the psd-ness of `BB*`/`B*B` (C2-49) is Mathlib's
  `Matrix.posSemidef_mul_conjTranspose_self`/`posSemidef_conjTranspose_mul_self`;
* `frobenius_norm_sq_eq_sum_singularValues_sq` — **book eq. (2.1.21)**
 (C2-51);
* `l2_opNorm_eq_sup_singularValues` — **book eq. (2.1.23)** (C2-53):
  the spectral norm is the largest singular value;
* `l2_opNorm_herm_consistency` — consistency of (2.1.22) and (2.1.23) on Hermitian
  matrices (C2-54);
* `l2_opNorm_sq_eq` — **book eq. (2.1.24)** (C2-56);
* `stableRank`, `one_le_stableRank`, `stableRank_le_rank`, `continuousAt_stableRank` —
  **book eq. (2.1.25)** and the surrounding claims (§2.1.15,
  C2-57/58/59). The claim `1 ≤ srank(B)` requires `B ≠ 0` (source issue SI-2: for
  `B = 0` the quotient is `0/0 = 0` and the display fails);
* `schattenOneNorm` — **book eq. (2.1.29)** (C2-68).  The book
  sums over `min{d₁,d₂}` indices; we sum over all of `d₂`, which agrees because at most
  `rank B ≤ min{d₁,d₂}` singular values are nonzero (`exists_svd`'s vanishing clause).
-/

namespace MatrixConcentration

open Matrix WithLp Finset
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section SingularValues

/-- **Book §2.1.13** (C2-47): the singular values of a rectangular matrix, realized in
the standard way as the square roots of the eigenvalues of the psd matrix `B*B`
(unsorted; `exists_svd` provides the book's weakly-decreasing arrangement). Implicit
source declaration. -/
noncomputable def singularValues (B : Matrix m n ℂ) : n → ℝ :=
  fun i => √((Matrix.isHermitian_conjTranspose_mul_self B).eigenvalues i)

/-- Lean implementation helper: singular values are nonnegative. -/
lemma singularValues_nonneg (B : Matrix m n ℂ) (i : n) : 0 ≤ singularValues B i :=
  Real.sqrt_nonneg _

/-- Lean implementation helper: the squared singular values are the eigenvalues of `BᴴB`. -/
lemma sq_singularValues (B : Matrix m n ℂ) (i : n) :
    singularValues B i ^ 2 = (Matrix.isHermitian_conjTranspose_mul_self B).eigenvalues i :=
  Real.sq_sqrt ((Matrix.posSemidef_conjTranspose_mul_self B).eigenvalues_nonneg i)

/-- **Book §2.1.13 (C2-47, well-definedness)**: the multiset of squared singular values is
the eigenvalue multiset of `B*B`, which by C2-11 (`eigenvalues_multiset_unique`) is
independent of the chosen decomposition. -/
theorem singularValues_sq_multiset_eq (B : Matrix m n ℂ) :
    Multiset.map (fun i => singularValues B i ^ 2) Finset.univ.val =
      Multiset.map (Matrix.isHermitian_conjTranspose_mul_self B).eigenvalues
        Finset.univ.val :=
  Multiset.map_congr rfl fun i _ => sq_singularValues B i

/-- **Book §2.1.13**: "The singular values of a positive-semidefinite matrix coincide with
its eigenvalues" (as multisets; the indexings need not agree). Explicit (prose) source
statement. -/
theorem singularValues_posSemidef_multiset_eq {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    Multiset.map (singularValues A) Finset.univ.val =
      Multiset.map hA.1.eigenvalues Finset.univ.val := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  -- `A*A = A·A = V · diag(λ²) · V*` from the spectral decomposition of `A`
  have hVV : (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
      (hA.1.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hA.1.eigenvectorUnitary.2
    simpa [star_eq_conjTranspose] using h
  have hAeq : Aᴴ * A = (hA.1.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (RCLike.ofReal ∘ fun i => hA.1.eigenvalues i ^ 2) *
      (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    have hd : diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) *
        diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) =
        (diagonal (RCLike.ofReal ∘ fun i => hA.1.eigenvalues i ^ 2) : Matrix n n ℂ) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      simp only [Function.comp_apply, ofReal_eq_complex]
      push_cast
      ring
    calc Aᴴ * A = A * A := by rw [show Aᴴ = A from hA.1]
    _ = ((hA.1.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) *
          (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ) *
        ((hA.1.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) *
          (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ) := by
      rw [← spectral_decomposition hA.1]
    _ = (hA.1.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) *
          (((hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
            (hA.1.eigenvectorUnitary : Matrix n n ℂ)) *
          (diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) *
            (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ)) := by
      simp only [← Matrix.mul_assoc]
    _ = (hA.1.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (RCLike.ofReal ∘ fun i => hA.1.eigenvalues i ^ 2) *
          (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
      rw [hVV, Matrix.one_mul, ← hd]
      simp only [← Matrix.mul_assoc]
  have hmult := eigenvalues_multiset_unique hH hA.1.eigenvectorUnitary.2 hAeq
  -- map √ through both sides
  calc Multiset.map (singularValues A) Finset.univ.val
      = Multiset.map (fun x => √x)
          (Multiset.map hH.eigenvalues Finset.univ.val) := by
        rw [Multiset.map_map]
        rfl
  _ = Multiset.map (fun x => √x)
        (Multiset.map (fun i => hA.1.eigenvalues i ^ 2) Finset.univ.val) := by
      rw [hmult]
  _ = Multiset.map hA.1.eigenvalues Finset.univ.val := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      show √(hA.1.eigenvalues i ^ 2) = hA.1.eigenvalues i
      exact Real.sqrt_sq (hA.eigenvalues_nonneg i)

/-- **Book eq. (2.1.21)** (§2.1.13, C2-51):
`‖B‖_F² = Σⱼ σⱼ(B)²`. Explicit (unnumbered) source statement; the source derives it
from unitary invariance, here it follows from the trace identity (2.1.8) and the
trace–eigenvalue identity of §2.1.7. -/
theorem frobenius_norm_sq_eq_sum_singularValues_sq (B : Matrix m n ℂ) :
    frobeniusNorm B ^ 2 = ∑ i, singularValues B i ^ 2 := by
  have h3 := trace_re_eq_sum_eigenvalues (Matrix.isHermitian_conjTranspose_mul_self B)
  rw [trace_conjTranspose_mul_self B, Complex.ofReal_re] at h3
  rw [h3]
  exact Finset.sum_congr rfl fun i _ => (sq_singularValues B i).symm

end SingularValues

section SpectralNorm

/-- **Book eq. (2.1.23)** (§2.1.14, C2-53): the spectral norm is
the largest singular value, `‖B‖ = σ₁(B)`. Explicit (unnumbered) source statement. -/
theorem l2_opNorm_eq_sup_singularValues [Nonempty n] (B : Matrix m n ℂ) :
    ‖B‖ = ⨆ i, singularValues B i := by
  have hH : (Bᴴ * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self B
  have h1 : ‖Bᴴ * B‖ = lambdaMax hH :=
    posSemidef_l2_opNorm_eq_lambdaMax (Matrix.posSemidef_conjTranspose_mul_self B)
  have h3 : ‖B‖ = √(lambdaMax hH) := by
    rw [← h1, Matrix.l2_opNorm_conjTranspose_mul_self,
      Real.sqrt_mul_self (norm_nonneg B)]
  rw [h3]
  show √(⨆ i, hH.eigenvalues i) = ⨆ i, √(hH.eigenvalues i)
  exact Monotone.map_ciSup_of_continuousAt Real.continuous_sqrt.continuousAt
    (fun x y hxy => Real.sqrt_le_sqrt hxy) (Set.Finite.bddAbove (Set.finite_range _))

/-- **Book §2.1.14 (C2-54)**: "These two definitions are consistent" — on a Hermitian
matrix, the largest singular value (2.1.23) agrees with `max{λ_max, −λ_min}` (2.1.22).
Implicit source claim, obtained by chaining C2-52 and C2-53. -/
theorem l2_opNorm_herm_consistency [Nonempty n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (⨆ i, singularValues A i) = max (lambdaMax hA) (-(lambdaMin hA)) :=
  (l2_opNorm_eq_sup_singularValues A).symm.trans (l2_opNorm_eq_max_lambda hA)

/-- **Book eq. (2.1.24)** (§2.1.14, C2-56):
`‖B‖² = ‖BB*‖ = ‖B*B‖`. Explicit (unnumbered) source statement (first half proved in
`Prelude/OpNorm.lean`, second half is the Mathlib C*-identity). -/
theorem l2_opNorm_sq_eq (B : Matrix m n ℂ) :
    ‖B‖ ^ 2 = ‖B * Bᴴ‖ ∧ ‖B‖ ^ 2 = ‖Bᴴ * B‖ :=
  ⟨(l2_opNorm_sq_mul_conjTranspose_self B).symm,
    by rw [Matrix.l2_opNorm_conjTranspose_mul_self, sq]⟩

/-- Lean implementation helper: the spectral norm is dominated by the Frobenius norm
(used for the continuity claim C2-59; a special case of `‖B‖ ≤ ‖B‖_{S1}`-type
comparisons the book takes for granted). -/
lemma l2_opNorm_le_frobeniusNorm (B : Matrix m n ℂ) : ‖B‖ ≤ frobeniusNorm B := by
  rcases isEmpty_or_nonempty n with h | h
  · have hB0 : B = 0 := by
      ext i j
      exact h.elim j
    rw [hB0]
    simpa using frobeniusNorm_nonneg (0 : Matrix m n ℂ)
  · have hH : (Bᴴ * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self B
    have hPSD := Matrix.posSemidef_conjTranspose_mul_self B
    have hsq : ‖B‖ ^ 2 ≤ frobeniusNorm B ^ 2 := by
      have h1 : ‖Bᴴ * B‖ = lambdaMax hH := posSemidef_l2_opNorm_eq_lambdaMax hPSD
      have h2 : ‖B‖ ^ 2 = lambdaMax hH := by
        rw [← h1, Matrix.l2_opNorm_conjTranspose_mul_self, sq]
      have h3 := trace_re_eq_sum_eigenvalues hH
      rw [trace_conjTranspose_mul_self B, Complex.ofReal_re] at h3
      have h4 : lambdaMax hH ≤ ∑ i, hH.eigenvalues i := by
        have h5 := lambdaMax_le_trace_re_of_posSemidef hPSD
        rw [trace_conjTranspose_mul_self B, Complex.ofReal_re, h3] at h5
        exact h5
      rw [h2, h3]
      exact h4
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg B), Real.sqrt_sq (frobeniusNorm_nonneg B)] at this

/-- Lean implementation helper: the Frobenius norm is continuous (for the product
topology; the book's §2.1.4 remark that all norms give the same convergence). -/
lemma continuous_frobeniusNorm :
    Continuous (frobeniusNorm : Matrix m n ℂ → ℝ) := by
  have h : Continuous fun B : Matrix m n ℂ => ∑ i, ∑ j, ‖B i j‖ ^ 2 :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (Continuous.norm ((continuous_apply j).comp (continuous_apply i))).pow 2
  exact Real.continuous_sqrt.comp h

/-- Lean implementation helper: the spectral norm is a continuous function of the
matrix entries. -/
lemma continuous_l2_opNorm : Continuous (fun B : Matrix m n ℂ => ‖B‖) := by
  rw [continuous_iff_continuousAt]
  intro B₀
  have hg : Filter.Tendsto (fun X : Matrix m n ℂ => frobeniusNorm (X - B₀))
      (nhds B₀) (nhds 0) := by
    have hc : Continuous fun X : Matrix m n ℂ => frobeniusNorm (X - B₀) :=
      continuous_frobeniusNorm.comp (continuous_id.sub continuous_const)
    have h0 : frobeniusNorm (B₀ - B₀) = 0 := by
      simp [frobeniusNorm]
    have := hc.tendsto B₀
    rwa [h0] at this
  have hkey : Filter.Tendsto (fun X : Matrix m n ℂ => ‖X‖ - ‖B₀‖)
      (nhds B₀) (nhds 0) := by
    refine squeeze_zero_norm (fun X => ?_) hg
    calc ‖(‖X‖ - ‖B₀‖ : ℝ)‖ = |‖X‖ - ‖B₀‖| := Real.norm_eq_abs _
    _ ≤ ‖X - B₀‖ := abs_norm_sub_norm_le X B₀
    _ ≤ frobeniusNorm (X - B₀) := l2_opNorm_le_frobeniusNorm _
  have h := hkey.add_const ‖B₀‖
  show Filter.Tendsto (fun X : Matrix m n ℂ => ‖X‖) (nhds B₀) (nhds ‖B₀‖)
  simpa using h

end SpectralNorm

section StableRank

/-- **Book eq. (2.1.25)** (§2.1.15, C2-57): the stable rank
`srank(B) = ‖B‖_F² / ‖B‖²`. Implicit source declaration (definition). -/
noncomputable def stableRank (B : Matrix m n ℂ) : ℝ :=
  frobeniusNorm B ^ 2 / ‖B‖ ^ 2

/-- **Book §2.1.15 (C2-58, lower half)**: `1 ≤ srank(B)`. Explicit (unnumbered)
source statement.

Author note: Lean assumes `B ≠ 0`; the source states the display for all `B`, but at
`B = 0` the totalized quotient is `0 / 0 = 0`. -/
theorem one_le_stableRank {B : Matrix m n ℂ} (hB : B ≠ 0) : 1 ≤ stableRank B := by
  haveI hne : Nonempty n := by
    by_contra h
    exact hB (by ext i j; exact absurd ⟨j⟩ h)
  have hH : (Bᴴ * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self B
  have hPSD := Matrix.posSemidef_conjTranspose_mul_self B
  have hnorm : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  show (1 : ℝ) ≤ frobeniusNorm B ^ 2 / ‖B‖ ^ 2
  rw [le_div_iff₀ (by positivity), one_mul]
  calc ‖B‖ ^ 2 = lambdaMax hH := by
        rw [← posSemidef_l2_opNorm_eq_lambdaMax hPSD,
          Matrix.l2_opNorm_conjTranspose_mul_self, sq]
  _ ≤ ((Bᴴ * B).trace).re := lambdaMax_le_trace_re_of_posSemidef hPSD
  _ = frobeniusNorm B ^ 2 := by rw [trace_conjTranspose_mul_self B, Complex.ofReal_re]

/-- **Book §2.1.15 (C2-58, upper half)**: `srank(B) ≤ rank(B)`. Explicit (unnumbered)
source statement; proof reconstructed:
`‖B‖_F² = Σλᵢ(B*B) = Σ_{λᵢ≠0} λᵢ ≤ #{λᵢ ≠ 0}·λ_max = rank(B)·‖B‖²`.

Author note: Lean assumes `B ≠ 0` so division by `‖B‖²` is legitimate; at zero the
totalized stable-rank quotient is degenerate. -/
theorem stableRank_le_rank {B : Matrix m n ℂ} (hB : B ≠ 0) :
    stableRank B ≤ (B.rank : ℝ) := by
  haveI hne : Nonempty n := by
    by_contra h
    exact hB (by ext i j; exact absurd ⟨j⟩ h)
  have hH : (Bᴴ * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self B
  have hPSD := Matrix.posSemidef_conjTranspose_mul_self B
  have hnorm : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hlmax : lambdaMax hH = ‖B‖ ^ 2 := by
    rw [← posSemidef_l2_opNorm_eq_lambdaMax hPSD,
      Matrix.l2_opNorm_conjTranspose_mul_self, sq]
  have hfrob : frobeniusNorm B ^ 2 = ∑ i, hH.eigenvalues i := by
    have h3 := trace_re_eq_sum_eigenvalues hH
    rw [trace_conjTranspose_mul_self B, Complex.ofReal_re] at h3
    exact h3
  have hsum : ∑ i, hH.eigenvalues i ≤ (B.rank : ℝ) * ‖B‖ ^ 2 := by
    have hfilter : ∑ i ∈ Finset.univ.filter (fun i => hH.eigenvalues i ≠ 0),
        hH.eigenvalues i = ∑ i, hH.eigenvalues i := Finset.sum_filter_ne_zero _
    rw [← hfilter]
    have hbound : ∀ i ∈ Finset.univ.filter (fun i => hH.eigenvalues i ≠ 0),
        hH.eigenvalues i ≤ ‖B‖ ^ 2 :=
      fun i _ => (eigenvalues_le_lambdaMax hH i).trans_eq hlmax
    have h2 := Finset.sum_le_card_nsmul _ _ _ hbound
    have hcard : (Finset.univ.filter (fun i => hH.eigenvalues i ≠ 0)).card = B.rank := by
      rw [← Matrix.rank_conjTranspose_mul_self B, hH.rank_eq_card_non_zero_eigs,
        Fintype.card_subtype]
    rw [hcard, nsmul_eq_mul] at h2
    exact h2
  show frobeniusNorm B ^ 2 / ‖B‖ ^ 2 ≤ (B.rank : ℝ)
  rw [div_le_iff₀ (by positivity)]
  rw [hfrob]
  exact hsum

/-- **Book §2.1.15 (C2-59)**: "In contrast to the rank, the stable rank is a continuous
function of the matrix" — continuity at every `B ≠ 0`. Prose source remark, recovered.

Author note: the totalized quotient is discontinuous at `B = 0`, so Lean states
continuity only away from zero. -/
theorem continuousAt_stableRank {B : Matrix m n ℂ} (hB : B ≠ 0) :
    ContinuousAt (stableRank : Matrix m n ℂ → ℝ) B := by
  have hnorm : ‖B‖ ≠ 0 := norm_ne_zero_iff.mpr hB
  have h1 : ContinuousAt (fun X : Matrix m n ℂ => frobeniusNorm X ^ 2) B :=
    (continuous_frobeniusNorm.continuousAt).pow 2
  have h2 : ContinuousAt (fun X : Matrix m n ℂ => ‖X‖ ^ 2) B :=
    (continuous_l2_opNorm.continuousAt).pow 2
  exact h1.div h2 (pow_ne_zero 2 hnorm)

end StableRank

section Schatten

/-- **Book eq. (2.1.29)** (§2.1.17, C2-68): the Schatten 1-norm
`‖B‖_{S1} = Σⱼ σⱼ(B)`. The book sums the `min{d₁,d₂}` ordered singular values; summing
over all of `d₂` agrees since at most `rank B ≤ min{d₁,d₂}` of them are nonzero.
Implicit source declaration (quantity).

**Author note.** The norm axioms are supplied below by `schattenOneNorm_add_le`,
`schattenOneNorm_smul`, and `schattenOneNorm_eq_zero_iff`; the named
`schattenOneNormedAddCommGroup` deliberately avoids a conflicting global matrix
norm instance. -/
noncomputable def schattenOneNorm (B : Matrix m n ℂ) : ℝ :=
  ∑ i, singularValues B i

/-- Lean implementation helper: nonnegativity of the Schatten-one quantity. -/
lemma schattenOneNorm_nonneg (B : Matrix m n ℂ) : 0 ≤ schattenOneNorm B :=
  Finset.sum_nonneg fun i _ => singularValues_nonneg B i

end Schatten

section SVD

/-- **Book eq. (2.1.20)** (§2.1.13, C2-48), first half: an SVD
`B = UΣW*` yields `BB* = U(ΣΣ*)U*`. Explicit (unnumbered) source statement. -/
theorem svd_mul_conjTranspose {B S : Matrix m n ℂ} {U : Matrix m m ℂ}
    {W : Matrix n n ℂ} (_hU : U ∈ Matrix.unitaryGroup m ℂ)
    (hW : W ∈ Matrix.unitaryGroup n ℂ) (hB : B = U * S * Wᴴ) :
    B * Bᴴ = U * (S * Sᴴ) * Uᴴ := by
  have hWW : Wᴴ * W = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hW
    simpa [star_eq_conjTranspose] using h
  subst hB
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (U * S) Wᴴ W, hWW, Matrix.mul_one]

/-- **Book eq. (2.1.20), second half**: `B*B = W(Σ*Σ)W*`. Explicit (unnumbered) source
statement. -/
theorem svd_conjTranspose_mul {B S : Matrix m n ℂ} {U : Matrix m m ℂ}
    {W : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup m ℂ)
    (_hW : W ∈ Matrix.unitaryGroup n ℂ) (hB : B = U * S * Wᴴ) :
    Bᴴ * B = W * (Sᴴ * S) * Wᴴ := by
  have hUU : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    simpa [star_eq_conjTranspose] using h
  subst hB
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (W * Sᴴ) Uᴴ U, hUU, Matrix.mul_one]

/-- **Book eq. (2.1.19)** (§2.1.13, C2-46): every
`d₁ × d₂` complex matrix has a singular value decomposition `B = UΣW*` with `U`, `W`
unitary and `Σ` the rectangular matrix with the singular values `σ₁ ≥ σ₂ ≥ …` on the
main diagonal and zeros elsewhere; at most `min{d₁,d₂}` singular values are nonzero
(the `p ≤ i → σ i = 0` clause). Explicit (unnumbered) source statement, stated by the
source without proof; the proof below is the standard construction the source sketches
on p. 24 (eigendecomposition of `B*B`, normalization of the images, orthonormal
extension). -/
theorem exists_svd {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℂ) :
    ∃ (U : Matrix (Fin p) (Fin p) ℂ) (W : Matrix (Fin q) (Fin q) ℂ) (σ : Fin q → ℝ),
      U ∈ Matrix.unitaryGroup (Fin p) ℂ ∧
      W ∈ Matrix.unitaryGroup (Fin q) ℂ ∧
      (∀ i, 0 ≤ σ i) ∧ Antitone σ ∧
      (∃ e : Equiv.Perm (Fin q), σ = fun i => singularValues B (e i)) ∧
      (∀ i : Fin q, p ≤ (i : ℕ) → σ i = 0) ∧
      B = U * (Matrix.of fun (j : Fin p) (i : Fin q) =>
        if (j : ℕ) = (i : ℕ) then ((σ i : ℝ) : ℂ) else 0) * Wᴴ := by
  classical
  have hH : (Bᴴ * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self B
  have hlam0 : ∀ i, 0 ≤ hH.eigenvalues i :=
    (Matrix.posSemidef_conjTranspose_mul_self B).eigenvalues_nonneg
  set V : Matrix (Fin q) (Fin q) ℂ := (hH.eigenvectorUnitary : Matrix (Fin q) (Fin q) ℂ)
    with hVdef
  have hVV : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
    simpa [hVdef, star_eq_conjTranspose] using h
  -- the sorting permutation: arrange the eigenvalues of B*B in weakly decreasing order
  set τ : Equiv.Perm (Fin q) := Tuple.sort (fun i => -hH.eigenvalues i) with hτdef
  have hanti : Antitone fun i : Fin q => hH.eigenvalues (τ i) := by
    intro a b hab
    have h := Tuple.monotone_sort (fun i => -hH.eigenvalues i) hab
    simp only [Function.comp_apply] at h
    exact neg_le_neg_iff.mp h
  -- the eigenvector relation in matrix form
  have hHV : (Bᴴ * B) * V = V * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    conv_lhs => rw [spectral_decomposition hH, ← hVdef]
    calc V * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Vᴴ * V
        = V * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * (Vᴴ * V) := by
          rw [Matrix.mul_assoc]
    _ = V * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
          rw [hVV, Matrix.mul_one]
  -- inner products of the columns of B·V
  have hD : (B * V)ᴴ * (B * V) = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    have h1 : (B * V)ᴴ * (B * V) = Vᴴ * ((Bᴴ * B) * V) := by
      rw [Matrix.conjTranspose_mul]
      simp only [← Matrix.mul_assoc]
    rw [h1, hHV, ← Matrix.mul_assoc, hVV, Matrix.one_mul]
  have hDentry : ∀ a b : Fin q,
      (∑ k, (starRingEnd ℂ) ((B * V) k a) * (B * V) k b) =
        if a = b then ((hH.eigenvalues a : ℝ) : ℂ) else 0 := by
    intro a b
    have h : ((B * V)ᴴ * (B * V)) a b =
        if a = b then ((hH.eigenvalues a : ℝ) : ℂ) else 0 := by
      rw [hD, Matrix.diagonal_apply]
      rfl
    rw [Matrix.mul_apply] at h
    simp only [Matrix.conjTranspose_apply] at h
    exact h
  -- a column with zero eigenvalue is a zero column
  have hzerocol : ∀ a : Fin q, hH.eigenvalues a = 0 → ∀ k, (B * V) k a = 0 := by
    intro a ha k
    have h := hDentry a a
    rw [if_pos rfl, ha] at h
    have hc : star (fun k => (B * V) k a) ⬝ᵥ (fun k => (B * V) k a) = 0 := by
      show (∑ k, star ((B * V) k a) * (B * V) k a) = 0
      simpa using h
    rw [dotProduct_star_self_eq] at hc
    have hl2 : l2norm (fun k => (B * V) k a) = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp (Complex.ofReal_eq_zero.mp hc)
    by_contra hk
    exact absurd hl2 (ne_of_gt (l2norm_pos_of_ne_zero
      (fun h0 => hk (congrFun h0 k))))
  -- τ-permuted column inner products
  have hcinner : ∀ a b : Fin q,
      star (fun k => (B * V) k (τ a)) ⬝ᵥ (fun k => (B * V) k (τ b)) =
        if a = b then ((hH.eigenvalues (τ a) : ℝ) : ℂ) else 0 := by
    intro a b
    have h2 : star (fun k => (B * V) k (τ a)) ⬝ᵥ (fun k => (B * V) k (τ b)) =
        if τ a = τ b then ((hH.eigenvalues (τ a) : ℝ) : ℂ) else 0 :=
      hDentry (τ a) (τ b)
    rw [h2]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (fun h => hab (τ.injective h)), if_neg hab]
  -- normalized images
  set u : Fin q → (Fin p → ℂ) := fun i k =>
    (((√(hH.eigenvalues (τ i)) : ℝ) : ℂ))⁻¹ * (B * V) k (τ i) with hudef
  have huinner : ∀ a b : Fin q, hH.eigenvalues (τ a) ≠ 0 → hH.eigenvalues (τ b) ≠ 0 →
      star (u a) ⬝ᵥ u b = if a = b then 1 else 0 := by
    intro a b ha hb
    have hstep : star (u a) ⬝ᵥ u b =
        (((√(hH.eigenvalues (τ a)) : ℝ) : ℂ))⁻¹ *
          ((((√(hH.eigenvalues (τ b)) : ℝ) : ℂ))⁻¹ *
            (star (fun k => (B * V) k (τ a)) ⬝ᵥ fun k => (B * V) k (τ b))) := by
      show (∑ k, star (u a k) * u b k) = _
      rw [show (star (fun k => (B * V) k (τ a)) ⬝ᵥ fun k => (B * V) k (τ b)) =
        ∑ k, (starRingEnd ℂ) ((B * V) k (τ a)) * (B * V) k (τ b) from rfl]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      show (starRingEnd ℂ) ((((√(hH.eigenvalues (τ a)) : ℝ) : ℂ))⁻¹ *
        (B * V) k (τ a)) * ((((√(hH.eigenvalues (τ b)) : ℝ) : ℂ))⁻¹ *
          (B * V) k (τ b)) = _
      rw [map_mul, map_inv₀, Complex.conj_ofReal]
      ring
    rw [hstep, hcinner a b]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl]
      have hpos : 0 < hH.eigenvalues (τ a) := (hlam0 _).lt_of_ne (Ne.symm ha)
      have hs : (0 : ℝ) < √(hH.eigenvalues (τ a)) := Real.sqrt_pos.mpr hpos
      have hreal : (√(hH.eigenvalues (τ a)))⁻¹ *
          ((√(hH.eigenvalues (τ a)))⁻¹ * hH.eigenvalues (τ a)) = 1 := by
        field_simp
        exact (Real.sq_sqrt hpos.le).symm
      calc (((√(hH.eigenvalues (τ a)) : ℝ) : ℂ))⁻¹ *
          ((((√(hH.eigenvalues (τ a)) : ℝ) : ℂ))⁻¹ *
            ((hH.eigenvalues (τ a) : ℝ) : ℂ))
          = (((√(hH.eigenvalues (τ a)))⁻¹ *
              ((√(hH.eigenvalues (τ a)))⁻¹ * hH.eigenvalues (τ a)) : ℝ) : ℂ) := by
            push_cast
            ring
      _ = 1 := by rw [hreal]; norm_num
    · rw [if_neg hab, if_neg hab, mul_zero, mul_zero]
  -- the rank segment
  set S : Finset (Fin q) := Finset.univ.filter (fun i => hH.eigenvalues (τ i) ≠ 0)
    with hSdef
  set r : ℕ := S.card with hrdef
  have hdc : ∀ {a b : Fin q}, a ≤ b → hH.eigenvalues (τ b) ≠ 0 →
      hH.eigenvalues (τ a) ≠ 0 := by
    intro a b hab hb
    have hpos : 0 < hH.eigenvalues (τ b) := (hlam0 _).lt_of_ne (Ne.symm hb)
    exact ne_of_gt (lt_of_lt_of_le hpos (hanti hab))
  have hseg : ∀ i : Fin q, (i : ℕ) < r ↔ hH.eigenvalues (τ i) ≠ 0 := by
    intro i
    constructor
    · intro hir
      by_contra h0
      have hsub : S ⊆ Finset.Iio i := by
        intro b hb
        rw [Finset.mem_Iio]
        by_contra hbi
        rw [not_lt] at hbi
        exact (hdc hbi (Finset.mem_filter.mp hb).2) h0
      have hcard := Finset.card_le_card hsub
      rw [Fin.card_Iio] at hcard
      rw [← hrdef] at hcard
      omega
    · intro h0
      have hsub : Finset.Iic i ⊆ S := by
        intro a ha
        rw [Finset.mem_Iic] at ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdc ha h0⟩
      have hcard := Finset.card_le_card hsub
      rw [Fin.card_Iic] at hcard
      rw [← hrdef] at hcard
      omega
  have hrq : r ≤ q := by
    rw [hrdef, hSdef]
    exact le_trans (Finset.card_filter_le _ _)
      (le_of_eq (by rw [Finset.card_univ, Fintype.card_fin]))
  -- the normalized images with nonzero eigenvalue form an orthonormal family,
  -- hence r ≤ p
  have hONseg : Orthonormal ℂ
      (fun i : {i : Fin q // (i : ℕ) < r} => toLp 2 (u i)) := by
    rw [orthonormal_iff_ite]
    intro a b
    rw [inner_toLp_eq_dotProduct,
      huinner a b ((hseg a).mp a.2) ((hseg b).mp b.2)]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (fun h => hab (Subtype.ext h)), if_neg hab]
  have hrp : r ≤ p := by
    have hcard := hONseg.linearIndependent.fintype_card_le_finrank
    rw [finrank_euclideanSpace_fin] at hcard
    have hcount : Fintype.card {i : Fin q // (i : ℕ) < r} = r := by
      rw [Fintype.card_subtype]
      have heq : Finset.univ.filter (fun i : Fin q => (i : ℕ) < r) = S :=
        Finset.ext fun i => by simp [Finset.mem_filter, hseg i, hSdef]
      rw [heq, ← hrdef]
    rw [hcount] at hcard
    exact hcard
  -- extend to an orthonormal basis of ℂ^p
  set w : Fin p → EuclideanSpace ℂ (Fin p) := fun j =>
    if h : (j : ℕ) < r then toLp 2 (u ⟨(j : ℕ), lt_of_lt_of_le h hrq⟩) else 0
    with hwdef
  have hONw : Orthonormal ℂ (Set.restrict {j : Fin p | (j : ℕ) < r} w) := by
    rw [orthonormal_iff_ite]
    intro a b
    have hwa : Set.restrict {j : Fin p | (j : ℕ) < r} w a =
        toLp 2 (u ⟨((a : Fin p) : ℕ), lt_of_lt_of_le a.2 hrq⟩) := by
      show w (a : Fin p) = _
      simp only [hwdef]
      exact dif_pos a.2
    have hwb : Set.restrict {j : Fin p | (j : ℕ) < r} w b =
        toLp 2 (u ⟨((b : Fin p) : ℕ), lt_of_lt_of_le b.2 hrq⟩) := by
      show w (b : Fin p) = _
      simp only [hwdef]
      exact dif_pos b.2
    have ha' : ((a : Fin p) : ℕ) < r := a.2
    have hb' : ((b : Fin p) : ℕ) < r := b.2
    rw [hwa, hwb, inner_toLp_eq_dotProduct,
      huinner ⟨((a : Fin p) : ℕ), lt_of_lt_of_le ha' hrq⟩
        ⟨((b : Fin p) : ℕ), lt_of_lt_of_le hb' hrq⟩
        ((hseg _).mp ha') ((hseg _).mp hb')]
    by_cases hab : a = b
    · subst hab; simp
    · have hne : ¬((⟨((a : Fin p) : ℕ), lt_of_lt_of_le ha' hrq⟩ : Fin q) =
          ⟨((b : Fin p) : ℕ), lt_of_lt_of_le hb' hrq⟩) :=
        fun h => hab (Subtype.ext (Fin.ext (Fin.mk_eq_mk.mp h)))
      rw [if_neg hne, if_neg hab]
  obtain ⟨bb, hbb⟩ := hONw.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_fin])
  -- assemble the unitary factors
  set U : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun k j => bb j k with hUdef
  have hUmem : U ∈ Matrix.unitaryGroup (Fin p) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext j j'
    have h := orthonormal_iff_ite.mp bb.orthonormal j j'
    rw [PiLp.inner_apply] at h
    simp only [RCLike.inner_apply] at h
    show (star U * U) j j' = (1 : Matrix (Fin p) (Fin p) ℂ) j j'
    rw [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.conjTranspose_apply, hUdef, Matrix.of_apply]
    simpa [RCLike.star_def, mul_comm] using h
  set W : Matrix (Fin q) (Fin q) ℂ := Matrix.of fun k i => V k (τ i) with hWdef
  have hWmem : W ∈ Matrix.unitaryGroup (Fin q) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i i'
    have h : (Vᴴ * V) (τ i) (τ i') = (1 : Matrix (Fin q) (Fin q) ℂ) (τ i) (τ i') := by
      rw [hVV]
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [Matrix.conjTranspose_apply] at h
    show (star W * W) i i' = (1 : Matrix (Fin q) (Fin q) ℂ) i i'
    rw [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.conjTranspose_apply, hWdef, Matrix.of_apply]
    rw [h]
    simp
  -- the key factorization identity, column by column
  have hBW : B * W = U * (Matrix.of fun (j : Fin p) (i : Fin q) =>
      if (j : ℕ) = (i : ℕ) then ((√(hH.eigenvalues (τ i)) : ℝ) : ℂ) else 0) := by
    ext k i
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have hL : (∑ l, B k l * W l i) = (B * V) k (τ i) := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun l _ => by simp only [hWdef, Matrix.of_apply]
    rw [hL]
    by_cases hip : (i : ℕ) < p
    · have hcollapse : (∑ j : Fin p, U k j *
          (Matrix.of fun (j : Fin p) (i : Fin q) =>
            if (j : ℕ) = (i : ℕ) then ((√(hH.eigenvalues (τ i)) : ℝ) : ℂ) else 0) j i) =
          U k ⟨(i : ℕ), hip⟩ * ((√(hH.eigenvalues (τ i)) : ℝ) : ℂ) := by
        rw [Finset.sum_eq_single (⟨(i : ℕ), hip⟩ : Fin p)]
        · simp
        · intro j _ hj
          simp only [Matrix.of_apply]
          rw [if_neg (fun h => hj (Fin.ext h)), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [hcollapse]
      by_cases hir : (i : ℕ) < r
      · have hj₀ : (⟨(i : ℕ), hip⟩ : Fin p) ∈ {j : Fin p | (j : ℕ) < r} := hir
        have hbj := hbb _ hj₀
        have hwj : w (⟨(i : ℕ), hip⟩ : Fin p) =
            toLp 2 (u ⟨(i : ℕ), lt_of_lt_of_le hir hrq⟩) := by
          simp only [hwdef]
          exact dif_pos hir
        have hidx : (⟨(i : ℕ), lt_of_lt_of_le hir hrq⟩ : Fin q) = i := Fin.ext rfl
        have hUentry : U k ⟨(i : ℕ), hip⟩ = u i k := by
          simp only [hUdef, Matrix.of_apply]
          rw [hbj, hwj, hidx]
        rw [hUentry]
        simp only [hudef]
        have hs0 : ((√(hH.eigenvalues (τ i)) : ℝ) : ℂ) ≠ 0 := by
          have hpos : 0 < hH.eigenvalues (τ i) :=
            (hlam0 _).lt_of_ne (Ne.symm ((hseg i).mp hir))
          exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
        field_simp
      · have hlz : hH.eigenvalues (τ i) = 0 := by
          by_contra hne
          exact hir ((hseg i).mpr hne)
        rw [hzerocol (τ i) hlz k, hlz, Real.sqrt_zero]
        simp
    · have hR : (∑ j : Fin p, U k j *
          (Matrix.of fun (j : Fin p) (i : Fin q) =>
            if (j : ℕ) = (i : ℕ) then ((√(hH.eigenvalues (τ i)) : ℝ) : ℂ) else 0) j i)
          = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        simp only [Matrix.of_apply]
        have hne : ¬((j : ℕ) = (i : ℕ)) := fun h => hip (h ▸ j.2)
        rw [if_neg hne, mul_zero]
      rw [hR]
      have hlz : hH.eigenvalues (τ i) = 0 := by
        by_contra hne
        have h1 := (hseg i).mpr hne
        omega
      exact hzerocol (τ i) hlz k
  -- conclude
  have hWW' : W * Wᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hWmem
    simpa [Matrix.star_eq_conjTranspose] using h
  refine ⟨U, W, fun i => √(hH.eigenvalues (τ i)), hUmem, hWmem,
    fun i => Real.sqrt_nonneg _,
    fun a b hab => Real.sqrt_le_sqrt (hanti hab),
    ⟨τ, rfl⟩,
    fun i hpi => ?_, ?_⟩
  · have hlz : hH.eigenvalues (τ i) = 0 := by
      by_contra hne
      have h1 := (hseg i).mpr hne
      omega
    show √(hH.eigenvalues (τ i)) = 0
    rw [hlz, Real.sqrt_zero]
  · calc B = B * (W * Wᴴ) := by rw [hWW', Matrix.mul_one]
    _ = (B * W) * Wᴴ := by rw [Matrix.mul_assoc]
    _ = _ := by rw [hBW]

end SVD

section SchattenNormAPI

/-- **Book eq. (2.1.29), norm API:** scalar multiplication scales the singular-value
multiset by the scalar norm. -/
theorem singularValues_smul_multiset (a : ℂ) (B : Matrix m n ℂ) :
    Multiset.map (singularValues (a • B)) Finset.univ.val =
      Multiset.map (fun i => ‖a‖ * singularValues B i) Finset.univ.val := by
  classical
  let hB : (Bᴴ * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self B
  let hC : ((a • B)ᴴ * (a • B)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self (a • B)
  have hmat : (a • B)ᴴ * (a • B) =
      (hB.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ fun i => ‖a‖ ^ 2 * hB.eigenvalues i) *
        (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    calc
      (a • B)ᴴ * (a • B) = (‖a‖ ^ 2 : ℂ) • (Bᴴ * B) := by
        rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        change ((starRingEnd ℂ) a * a) • (Bᴴ * B) = _
        rw [RCLike.conj_mul]
        rfl
      _ = (‖a‖ ^ 2 : ℂ) •
          ((hB.eigenvectorUnitary : Matrix n n ℂ) *
            diagonal (RCLike.ofReal ∘ hB.eigenvalues) *
            (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ) := by
              rw [← spectral_decomposition hB]
      _ = _ := by
        rw [← Matrix.smul_mul, ← Matrix.mul_smul]
        congr 2
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Function.comp_apply]
        · simp [Matrix.diagonal_apply_ne _ hij]
  have heig :
      Multiset.map (fun i => ‖a‖ ^ 2 * hB.eigenvalues i) Finset.univ.val =
        Multiset.map hC.eigenvalues Finset.univ.val :=
    eigenvalues_multiset_unique hC hB.eigenvectorUnitary.2 hmat
  calc
    Multiset.map (singularValues (a • B)) Finset.univ.val =
        Multiset.map Real.sqrt
          (Multiset.map hC.eigenvalues Finset.univ.val) := by
            rw [Multiset.map_map]
            rfl
    _ = Multiset.map Real.sqrt
          (Multiset.map (fun i => ‖a‖ ^ 2 * hB.eigenvalues i) Finset.univ.val) := by
            rw [heig]
    _ = Multiset.map (fun i => ‖a‖ * singularValues B i) Finset.univ.val := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      change √(‖a‖ ^ 2 * hB.eigenvalues i) =
        ‖a‖ * √(hB.eigenvalues i)
      rw [Real.sqrt_mul (sq_nonneg ‖a‖), Real.sqrt_sq (norm_nonneg a)]

/-- **Book eq. (2.1.29), norm API:** complex homogeneity of the Schatten-one
quantity. -/
theorem schattenOneNorm_smul (a : ℂ) (B : Matrix m n ℂ) :
    schattenOneNorm (a • B) = ‖a‖ * schattenOneNorm B := by
  have h := congrArg Multiset.sum (singularValues_smul_multiset a B)
  simpa [schattenOneNorm, Finset.mul_sum] using h

/-- **Book eq. (2.1.29), norm API:** the Schatten-one quantity separates
matrices. -/
theorem schattenOneNorm_eq_zero_iff (B : Matrix m n ℂ) :
    schattenOneNorm B = 0 ↔ B = 0 := by
  constructor
  · intro hzero
    have hs : ∀ i, singularValues B i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => singularValues_nonneg B i).mp
        hzero i (Finset.mem_univ i)
    have hfrob : frobeniusNorm B ^ 2 = 0 := by
      rw [frobenius_norm_sq_eq_sum_singularValues_sq]
      simp [hs]
    have hentries : ∑ i, ∑ j, ‖B i j‖ ^ 2 = 0 := by
      rw [← frobeniusNorm_sq]
      exact hfrob
    ext i j
    have hi : ∑ j, ‖B i j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sq_nonneg ‖B i j‖).mp hentries i
          (Finset.mem_univ i)
    have hij : ‖B i j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖B i j‖).mp hi j
        (Finset.mem_univ j)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hij)
  · rintro rfl
    simpa using
      (schattenOneNorm_smul (m := m) (n := n) (0 : ℂ) (0 : Matrix m n ℂ))

/-! The remaining norm axiom is proved first on `Fin` indices by finite-dimensional
trace duality, then transported along finite-type reindexing.  All auxiliary duality
declarations are private so the public API remains representation-independent. -/

/-- Lean implementation helper: rectangular entries are dominated by the L2 operator norm. -/
private lemma norm_entry_le_l2_opNorm_rect_ch2 {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] (A : Matrix p q ℂ) (i : p) (j : q) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h := norm_dotProduct_mulVec_le A (Pi.single i 1) (Pi.single j 1)
  have h1 : star (Pi.single i (1 : ℂ)) ⬝ᵥ (A *ᵥ Pi.single j 1) = A i j := by
    rw [Matrix.mulVec_single]
    show (∑ k, star ((Pi.single i (1 : ℂ) : p → ℂ) k) * (A k j * 1)) = A i j
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  haveI : Nonempty p := ⟨i⟩
  haveI : Nonempty q := ⟨j⟩
  have hsingle1 : l2norm (Pi.single i (1 : ℂ) : p → ℂ) = 1 := by
    rw [l2norm_eq_sqrt_sum]
    have hs : (∑ k, ‖(Pi.single i (1 : ℂ) : p → ℂ) k‖ ^ 2) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        simp [Pi.single_eq_of_ne hki]
      · exact fun h => absurd (Finset.mem_univ i) h
    rw [hs, Real.sqrt_one]
  have hsingle2 : l2norm (Pi.single j (1 : ℂ) : q → ℂ) = 1 := by
    rw [l2norm_eq_sqrt_sum]
    have hs : (∑ k, ‖(Pi.single j (1 : ℂ) : q → ℂ) k‖ ^ 2) = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj
        simp [Pi.single_eq_of_ne hkj]
      · exact fun h => absurd (Finset.mem_univ j) h
    rw [hs, Real.sqrt_one]
  rw [h1, hsingle1, hsingle2] at h
  simpa using h

/-- Lean implementation helper: the trace/operator-norm half of Schatten-one duality on
rectangular `Fin` matrices. -/
private theorem abs_trace_mul_le_schattenOne_ch2 {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p) ℂ) :
    ‖(A * C).trace‖ ≤ ‖A‖ * schattenOneNorm C := by
  classical
  obtain ⟨U, W, σ, hU, hW, hσ0, -, ⟨e, hσe⟩, -, hC⟩ := exists_svd C
  set Sig : Matrix (Fin q) (Fin p) ℂ := Matrix.of fun (j : Fin q) (i : Fin p) =>
    if (j : ℕ) = (i : ℕ) then ((σ i : ℝ) : ℂ) else 0 with hSigdef
  set N : Matrix (Fin p) (Fin q) ℂ := Wᴴ * A * U with hNdef
  have htr : (A * C).trace = (N * Sig).trace := by
    rw [hC]
    rw [show A * (U * Sig * Wᴴ) = A * U * Sig * Wᴴ from by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm (A * U * Sig) Wᴴ]
    rw [show Wᴴ * (A * U * Sig) = (Wᴴ * A * U) * Sig from by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]]
  have hNnorm : ‖N‖ = ‖A‖ := by
    rw [hNdef, Matrix.mul_assoc,
      show (Wᴴ : Matrix (Fin p) (Fin p) ℂ) = star W from
        (Matrix.star_eq_conjTranspose W).symm,
      l2_opNorm_unitary_mul (Unitary.star_mem hW) (A * U),
      l2_opNorm_mul_unitary A hU]
  have hentry : ∀ i : Fin p, ‖(N * Sig) i i‖ ≤ ‖A‖ * σ i := by
    intro i
    rw [Matrix.mul_apply]
    calc ‖∑ j, N i j * Sig j i‖ ≤ ∑ j, ‖N i j * Sig j i‖ :=
          norm_sum_le _ _
    _ ≤ ∑ j : Fin q, (if (j : ℕ) = (i : ℕ) then ‖A‖ * σ i else 0) := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hji : (j : ℕ) = (i : ℕ)
        · rw [if_pos hji, hSigdef]
          rw [show (Matrix.of fun (j : Fin q) (i : Fin p) =>
            if (j : ℕ) = (i : ℕ) then ((σ i : ℝ) : ℂ) else 0) j i =
            ((σ i : ℝ) : ℂ) from by rw [Matrix.of_apply, if_pos hji]]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hσ0 i)]
          refine mul_le_mul_of_nonneg_right ?_ (hσ0 i)
          rw [← hNnorm]
          exact norm_entry_le_l2_opNorm_rect_ch2 N i j
        · rw [if_neg hji, hSigdef]
          rw [show (Matrix.of fun (j : Fin q) (i : Fin p) =>
            if (j : ℕ) = (i : ℕ) then ((σ i : ℝ) : ℂ) else 0) j i =
            0 from by rw [Matrix.of_apply, if_neg hji]]
          rw [mul_zero, norm_zero]
    _ ≤ ‖A‖ * σ i := by
        have hAσ : 0 ≤ ‖A‖ * σ i := mul_nonneg (norm_nonneg A) (hσ0 i)
        by_cases hi : (i : ℕ) < q
        · rw [Finset.sum_eq_single (⟨(i : ℕ), hi⟩ : Fin q)]
          · rw [if_pos rfl]
          · intro b _ hb
            refine if_neg fun hbi => hb (Fin.ext hbi)
          · intro hmem
            exact absurd (Finset.mem_univ _) hmem
        · have hz : (∑ j : Fin q,
              (if (j : ℕ) = (i : ℕ) then ‖A‖ * σ i else 0)) = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            refine if_neg fun hji => ?_
            exact hi (hji ▸ j.isLt)
          rw [hz]
          exact hAσ
  rw [htr]
  calc ‖(N * Sig).trace‖ = ‖∑ i, (N * Sig) i i‖ := by rw [Matrix.trace]; rfl
  _ ≤ ∑ i, ‖(N * Sig) i i‖ := norm_sum_le _ _
  _ ≤ ∑ i, ‖A‖ * σ i := Finset.sum_le_sum fun i _ => hentry i
  _ = ‖A‖ * ∑ i, σ i := by rw [Finset.mul_sum]
  _ = ‖A‖ * schattenOneNorm C := by
      congr 1
      rw [schattenOneNorm, hσe]
      exact Fintype.sum_equiv e _ _ fun i => rfl

/-- Lean implementation helper: the rectangular identity used as a polar-duality witness. -/
private def schattenRectId (p q : ℕ) : Matrix (Fin p) (Fin q) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

/-- Lean implementation helper: Gram matrix of the rectangular identity. -/
private lemma schattenRectId_conjTranspose_mul (p q : ℕ) :
    (schattenRectId p q)ᴴ * schattenRectId p q =
      Matrix.diagonal (fun j : Fin q => if (j : ℕ) < p then (1 : ℂ) else 0) := by
  classical
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.conjTranspose_apply, schattenRectId, Matrix.of_apply]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    by_cases hip : (i : ℕ) < p
    · rw [if_pos hip]
      rw [Finset.sum_eq_single (⟨(i : ℕ), hip⟩ : Fin p)]
      · simp
      · intro b _ hb
        have hbi : (b : ℕ) ≠ (i : ℕ) := fun h => hb (Fin.ext h)
        simp [hbi]
      · simp
    · rw [if_neg hip]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hki : (k : ℕ) ≠ (i : ℕ) := fun h => hip (h ▸ k.isLt)
      simp [hki]
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hki : (k : ℕ) = (i : ℕ)
    · have hijv : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
      simp [hki, hijv]
    · simp [hki]

/-- Lean implementation helper: the rectangular identity has operator norm at most one. -/
private lemma schattenRectId_norm_le_one (p q : ℕ) : ‖schattenRectId p q‖ ≤ 1 := by
  classical
  have hdiag : ‖(Matrix.diagonal (fun j : Fin q =>
      if (j : ℕ) < p then (1 : ℂ) else 0) : Matrix (Fin q) (Fin q) ℂ)‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun j => ?_
    split <;> simp
  have hsq : ‖schattenRectId p q‖ ^ 2 ≤ 1 := by
    rw [(l2_opNorm_sq_eq (schattenRectId p q)).2, schattenRectId_conjTranspose_mul]
    exact hdiag
  nlinarith [norm_nonneg (schattenRectId p q)]

/-- Lean implementation helper: an SVD supplies a unit-operator-norm trace witness for
the Schatten-one norm. -/
private lemma exists_schatten_trace_dual_witness {p q : ℕ}
    (T : Matrix (Fin p) (Fin q) ℂ) :
    ∃ A : Matrix (Fin q) (Fin p) ℂ,
      ‖A‖ ≤ 1 ∧ (A * T).trace = (schattenOneNorm T : ℂ) := by
  classical
  obtain ⟨U, W, σ, hU, hW, hσ0, -, ⟨e, hσe⟩, hσvanish, hT⟩ := exists_svd T
  let P : Matrix (Fin p) (Fin q) ℂ := schattenRectId p q
  let A : Matrix (Fin q) (Fin p) ℂ := W * Pᴴ * Uᴴ
  refine ⟨A, ?_, ?_⟩
  · dsimp only [A]
    have hWstar : Wᴴ ∈ Matrix.unitaryGroup (Fin q) ℂ := by
      simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hW
    have hUstar : Uᴴ ∈ Matrix.unitaryGroup (Fin p) ℂ := by
      simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU
    calc
      ‖W * Pᴴ * Uᴴ‖ = ‖W * Pᴴ‖ := l2_opNorm_mul_unitary _ hUstar
      _ = ‖Pᴴ‖ := l2_opNorm_unitary_mul hW _
      _ = ‖P‖ := Matrix.l2_opNorm_conjTranspose P
      _ ≤ 1 := schattenRectId_norm_le_one p q
  · let Sig : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun (j : Fin p) (i : Fin q) =>
      if (j : ℕ) = (i : ℕ) then ((σ i : ℝ) : ℂ) else 0
    have hUU : Uᴴ * U = 1 := by
      have h := Matrix.mem_unitaryGroup_iff'.mp hU
      simpa [star_eq_conjTranspose] using h
    have hWW : Wᴴ * W = 1 := by
      have h := Matrix.mem_unitaryGroup_iff'.mp hW
      simpa [star_eq_conjTranspose] using h
    have hcyc : (A * T).trace = (Pᴴ * Sig).trace := by
      rw [hT]
      change ((W * Pᴴ * Uᴴ) * (U * Sig * Wᴴ)).trace = _
      rw [show (W * Pᴴ * Uᴴ) * (U * Sig * Wᴴ) =
          W * (Pᴴ * Sig) * Wᴴ by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Uᴴ U (Sig * Wᴴ), hUU, Matrix.one_mul]]
      rw [Matrix.trace_mul_cycle, hWW, Matrix.one_mul]
    rw [hcyc]
    have htrace : (Pᴴ * Sig).trace = ∑ i, (σ i : ℂ) := by
      rw [Matrix.trace]
      refine Finset.sum_congr rfl fun i _ => ?_
      change (Pᴴ * Sig) i i = (σ i : ℂ)
      rw [Matrix.mul_apply]
      by_cases hip : (i : ℕ) < p
      · rw [Finset.sum_eq_single (⟨(i : ℕ), hip⟩ : Fin p)]
        · simp [P, schattenRectId, Sig]
        · intro b _ hb
          have hbi : (b : ℕ) ≠ (i : ℕ) := fun h => hb (Fin.ext h)
          simp [P, schattenRectId, Sig, hbi]
        · simp
      · have hsig : σ i = 0 := hσvanish i (Nat.le_of_not_gt hip)
        rw [hsig]
        refine Finset.sum_eq_zero fun k _ => ?_
        simp [P, schattenRectId, Sig, hsig]
    rw [htrace]
    calc
      ∑ i, (σ i : ℂ) = ((∑ i, σ i : ℝ) : ℂ) := by push_cast; rfl
      _ = (schattenOneNorm T : ℂ) := by
        congr 1
        rw [schattenOneNorm, hσe]
        exact Fintype.sum_equiv e _ _ fun i => rfl

/-- Lean implementation helper: triangle inequality on canonical finite index types. -/
private theorem schattenOneNorm_add_le_fin {p q : ℕ}
    (B C : Matrix (Fin p) (Fin q) ℂ) :
    schattenOneNorm (B + C) ≤ schattenOneNorm B + schattenOneNorm C := by
  obtain ⟨A, hA, hAT⟩ := exists_schatten_trace_dual_witness (B + C)
  have hB := abs_trace_mul_le_schattenOne_ch2 A B
  have hC := abs_trace_mul_le_schattenOne_ch2 A C
  have hnonB := schattenOneNorm_nonneg B
  have hnonC := schattenOneNorm_nonneg C
  have hsplit : A * (B + C) = A * B + A * C := Matrix.mul_add _ _ _
  calc
    schattenOneNorm (B + C) = ‖(A * (B + C)).trace‖ := by
      rw [hAT, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (schattenOneNorm_nonneg (B + C))]
    _ = ‖(A * B).trace + (A * C).trace‖ := by rw [hsplit, Matrix.trace_add]
    _ ≤ ‖(A * B).trace‖ + ‖(A * C).trace‖ := norm_add_le _ _
    _ ≤ ‖A‖ * schattenOneNorm B + ‖A‖ * schattenOneNorm C := add_le_add hB hC
    _ ≤ schattenOneNorm B + schattenOneNorm C := by
      exact add_le_add
        (mul_le_of_le_one_left hnonB hA)
        (mul_le_of_le_one_left hnonC hA)

/-- Lean implementation helper: reindexing a Hermitian matrix along an equivalence
preserves its eigenvalue multiset. -/
private lemma eigenvalues_multiset_reindex_eq
    {n n' : Type*} [Fintype n] [Fintype n']
    [DecidableEq n] [DecidableEq n']
    {A : Matrix n n ℂ} {A' : Matrix n' n' ℂ}
    (hA : A.IsHermitian) (hA' : A'.IsHermitian)
    (e : n ≃ n') (h : A' = Matrix.reindex e e A) :
    Multiset.map hA'.eigenvalues Finset.univ.val =
      Multiset.map hA.eigenvalues Finset.univ.val := by
  apply Multiset.map_injective
    (RCLike.ofReal_injective : Function.Injective (RCLike.ofReal : ℝ → ℂ))
  rw [Multiset.map_map, Multiset.map_map]
  rw [← hA'.roots_charpoly_eq_eigenvalues,
    ← hA.roots_charpoly_eq_eigenvalues, h, Matrix.charpoly_reindex]

/-- Lean implementation helper: row and column reindexing transports the Gram matrix. -/
private lemma schattenGram_reindex
    {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n']
    (em : m ≃ m') (en : n ≃ n') (B : Matrix m n ℂ) :
    (Matrix.reindex em en B)ᴴ * Matrix.reindex em en B =
      Matrix.reindex en en (Bᴴ * B) := by
  rw [Matrix.conjTranspose_reindex]
  simpa only [Matrix.reindex_apply] using
    (Matrix.submatrix_mul_equiv Bᴴ B en.symm em.symm en.symm)

/-- **Book eq. (2.1.29), norm API:** the Schatten-one norm is invariant under
reindexing rows and columns along equivalences. -/
theorem schattenOneNorm_reindex
    {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n']
    [DecidableEq m] [DecidableEq n]
    [DecidableEq m'] [DecidableEq n']
    (em : m ≃ m') (en : n ≃ n') (B : Matrix m n ℂ) :
    schattenOneNorm (Matrix.reindex em en B) = schattenOneNorm B := by
  let B' : Matrix m' n' ℂ := Matrix.reindex em en B
  let hB : (Bᴴ * B).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self B
  let hB' : (B'ᴴ * B').IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self B'
  have hgram : B'ᴴ * B' = Matrix.reindex en en (Bᴴ * B) := by
    exact schattenGram_reindex em en B
  have heig :
      Multiset.map hB'.eigenvalues Finset.univ.val =
        Multiset.map hB.eigenvalues Finset.univ.val :=
    eigenvalues_multiset_reindex_eq hB hB' en hgram
  have hsv :
      Multiset.map (singularValues B') Finset.univ.val =
        Multiset.map (singularValues B) Finset.univ.val := by
    calc
      Multiset.map (singularValues B') Finset.univ.val =
          Multiset.map Real.sqrt
            (Multiset.map hB'.eigenvalues Finset.univ.val) := by
        rw [Multiset.map_map]
        rfl
      _ = Multiset.map Real.sqrt
            (Multiset.map hB.eigenvalues Finset.univ.val) := by rw [heig]
      _ = Multiset.map (singularValues B) Finset.univ.val := by
        rw [Multiset.map_map]
        rfl
  have hsum := congrArg Multiset.sum hsv
  simpa [schattenOneNorm, B'] using hsum

/-- **Book eq. (2.1.29), norm API:** triangle inequality for the Schatten-one norm.
The proof uses finite-dimensional SVD trace duality and then transports from `Fin`
indices to arbitrary finite index types. -/
theorem schattenOneNorm_add_le (B C : Matrix m n ℂ) :
    schattenOneNorm (B + C) ≤ schattenOneNorm B + schattenOneNorm C := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  calc
    schattenOneNorm (B + C) =
        schattenOneNorm (Matrix.reindex em en (B + C)) :=
      (schattenOneNorm_reindex em en (B + C)).symm
    _ = schattenOneNorm
        (Matrix.reindex em en B + Matrix.reindex em en C) := by rfl
    _ ≤ schattenOneNorm (Matrix.reindex em en B) +
        schattenOneNorm (Matrix.reindex em en C) :=
      schattenOneNorm_add_le_fin _ _
    _ = schattenOneNorm B + schattenOneNorm C := by
      rw [schattenOneNorm_reindex em en B, schattenOneNorm_reindex em en C]

/-- **Book eq. (2.1.29), bundled norm:** the Schatten-one norm as a named
`AddGroupNorm`. It is deliberately not installed as a global matrix norm instance. -/
noncomputable def schattenOneAddGroupNorm : AddGroupNorm (Matrix m n ℂ) where
  toFun := schattenOneNorm
  map_zero' := by
    have h := schattenOneNorm_smul (m := m) (n := n) (0 : ℂ)
      (0 : Matrix m n ℂ)
    simpa using h
  add_le' := schattenOneNorm_add_le
  neg' := by
    intro B
    simpa using schattenOneNorm_smul (m := m) (n := n) (-1 : ℂ) B
  eq_zero_of_map_eq_zero' := fun B => (schattenOneNorm_eq_zero_iff B).mp

/-- **Book eq. (2.1.29), bundled norm:** the named normed additive-group structure
induced by `schattenOneAddGroupNorm`; it is not a global instance. -/
@[reducible] noncomputable def schattenOneNormedAddCommGroup :
    NormedAddCommGroup (Matrix m n ℂ) :=
  schattenOneAddGroupNorm.toNormedAddCommGroup

/-- **Book eq. (2.1.29), value correspondence:** the norm of the named
Schatten-one structure is exactly `schattenOneNorm`. -/
theorem schattenOneNorm_eq_bundled_norm (B : Matrix m n ℂ) :
    schattenOneNorm B =
      @norm (Matrix m n ℂ) schattenOneNormedAddCommGroup.toNorm B :=
  rfl

end SchattenNormAPI

end MatrixConcentration


set_option linter.unusedSectionVars false

/-!
# The Hermitian dilation (Tropp §2.1.16)

**Definition 2.1.5 (Hermitian Dilation)**: `H(B) = [[0, B], [B*, 0]]`. The dilation is
represented on the sum type `m ⊕ n` (rather than `Fin (d₁ + d₂)`); this representation
difference is recorded in the statement audit.

* `hermDilation` — Definition 2.1.5 (with the codomain obligation
  `isHermitian_hermDilation`);
* `hermDilation_add`, `hermDilation_smul_real` — "It is clear that the Hermitian
  dilation is a real-linear map" (p. 24, implicit claim);
* `hermDilation_sq` — book eq. **(2.1.27)**;
* `l2_opNorm_hermDilation` — "As a consequence, `‖H(B)‖ = ‖B‖`" (p. 25);
* `lambdaMax_hermDilation` — book eq. **(2.1.28)**:
  `λ_max(H(B)) = ‖H(B)‖ = ‖B‖`. The source sketches a proof via the SVD and the
  Rayleigh characterization; we give a mathematically equivalent argument via the
  sign-flip symmetry `J H(B) J* = −H(B)` (with `J = diag(I, −I)` unitary), which shows
  the spectrum of `H(B)` is symmetric about `0` — the same spectral fact the source's
  sketch extracts from the SVD. See the statement/proof audit.
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Book Definition 2.1.5 (Hermitian Dilation)**, §2.1.16: the map
`H(B) = [[0, B], [B*, 0]]` from `d₁ × d₂` matrices to Hermitian matrices of dimension
`d₁ + d₂`. Explicit source declaration. -/
def hermDilation (B : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  Matrix.fromBlocks 0 B Bᴴ 0

/-- **Book Definition 2.1.5, codomain obligation:** `H(B)` is Hermitian. Implicit source
declaration (hidden proof obligation). -/
lemma isHermitian_hermDilation (B : Matrix m n ℂ) : (hermDilation B).IsHermitian := by
  rw [hermDilation, Matrix.isHermitian_fromBlocks_iff]
  exact ⟨Matrix.isHermitian_zero, rfl, Matrix.conjTranspose_conjTranspose B,
    Matrix.isHermitian_zero⟩

/-- **Book §2.1.16, p. 24**: additivity of the Hermitian dilation. Implicit source
declaration ("It is clear that the Hermitian dilation is a real-linear map"). -/
lemma hermDilation_add (B C : Matrix m n ℂ) :
    hermDilation (B + C) = hermDilation B + hermDilation C := by
  rw [hermDilation, hermDilation, hermDilation, Matrix.conjTranspose_add,
    Matrix.fromBlocks_add, add_zero, add_zero]

/-- **Book §2.1.16, p. 24**: real-homogeneity of the Hermitian dilation. Implicit source
declaration. -/
lemma hermDilation_smul_real (α : ℝ) (B : Matrix m n ℂ) :
    hermDilation (α • B) = α • hermDilation B := by
  rw [hermDilation, hermDilation]
  have h1 : (α • B)ᴴ = α • Bᴴ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [h1, Matrix.fromBlocks_smul]
  simp

/-- **Book eq. (2.1.27)** (§2.1.16): the square of the
dilation is `[[BB*, 0], [0, B*B]]`. Explicit (unnumbered) source statement.

**Author note.** See `hermDilation_sq_eigenvalues_multiset` for the full
squared-spectrum consequence with multiplicities and zero eigenvalues. -/
theorem hermDilation_sq (B : Matrix m n ℂ) :
    hermDilation B * hermDilation B = Matrix.fromBlocks (B * Bᴴ) 0 0 (Bᴴ * B) := by
  rw [hermDilation, Matrix.fromBlocks_multiply]
  simp

/-- Lean implementation helper: the eigenvalue multiset of a Hermitian block-diagonal
matrix is the sum of the eigenvalue multisets of its diagonal blocks. -/
theorem eigenvalues_fromBlocks_diagonal_multiset {A : Matrix m m ℂ}
    {D : Matrix n n ℂ} (hA : A.IsHermitian) (hD : D.IsHermitian) :
    Multiset.map
        (show (Matrix.fromBlocks A 0 0 D).IsHermitian from by
          rw [Matrix.isHermitian_fromBlocks_iff]
          exact ⟨hA, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero, hD⟩).eigenvalues
        Finset.univ.val =
      Multiset.map hA.eigenvalues Finset.univ.val +
        Multiset.map hD.eigenvalues Finset.univ.val := by
  classical
  let hAD : (Matrix.fromBlocks A 0 0 D).IsHermitian := by
    rw [Matrix.isHermitian_fromBlocks_iff]
    exact ⟨hA, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero, hD⟩
  have hchar : (Matrix.fromBlocks A 0 0 D).charpoly = A.charpoly * D.charpoly := by
    rw [Matrix.charpoly_fromBlocks_zero₂₁]
  have hroots : (Matrix.fromBlocks A 0 0 D).charpoly.roots =
      A.charpoly.roots + D.charpoly.roots := by
    rw [hchar, Polynomial.roots_mul
      (mul_ne_zero A.charpoly_monic.ne_zero D.charpoly_monic.ne_zero)]
  rw [hAD.roots_charpoly_eq_eigenvalues, hA.roots_charpoly_eq_eigenvalues,
    hD.roots_charpoly_eq_eigenvalues] at hroots
  have hinj : Function.Injective (RCLike.ofReal : ℝ → ℂ) := RCLike.ofReal_injective
  apply Multiset.map_injective hinj
  simpa only [Multiset.map_add, Multiset.map_map] using hroots

/-- **Book §2.1.16, full squared spectrum:** with multiplicities, the squared
eigenvalues of `H(B)` are the squared singular values contributed by `B` and `Bᴴ`.
This is the multiset-strengthening of the earlier block-square statement
`hermDilation_sq`; see `hermDilation_eigenvalues_multiset` for the resulting
signed spectrum. -/
theorem hermDilation_sq_eigenvalues_multiset (B : Matrix m n ℂ) :
    Multiset.map (fun i => (isHermitian_hermDilation B).eigenvalues i ^ 2)
        Finset.univ.val =
      Multiset.map (fun i => singularValues Bᴴ i ^ 2) Finset.univ.val +
        Multiset.map (fun i => singularValues B i ^ 2) Finset.univ.val := by
  classical
  let hH := isHermitian_hermDilation B
  let hBB : (B * Bᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self B
  let hBtB : (Bᴴ * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self B
  let hblock : (Matrix.fromBlocks (B * Bᴴ) 0 0 (Bᴴ * B)).IsHermitian := by
    rw [Matrix.isHermitian_fromBlocks_iff]
    exact ⟨hBB, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero, hBtB⟩
  have hUstarU :
      (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ)ᴴ *
          (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
    simpa [star_eq_conjTranspose] using h
  have hsqdiag : hermDilation B * hermDilation B =
      (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ) *
        diagonal (RCLike.ofReal ∘ fun i => hH.eigenvalues i ^ 2) *
        (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ)ᴴ := by
    calc
      hermDilation B * hermDilation B =
          ((hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ) *
              diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
              (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ)ᴴ) *
            ((hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ) *
              diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
              (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ)ᴴ) := by
                rw [← spectral_decomposition hH]
      _ = (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ) *
            (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
              diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *
            (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ)ᴴ := by
              simp only [← Matrix.mul_assoc]
              rw [Matrix.mul_assoc
                ((hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ) *
                  diagonal (RCLike.ofReal ∘ hH.eigenvalues))
                (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ)ᴴ,
                hUstarU, Matrix.mul_one]
      _ = _ := by
            rw [Matrix.diagonal_mul_diagonal]
            congr 2
            ext i j
            by_cases hij : i = j
            · subst j
              simp [Function.comp_apply, pow_two]
            · simp [Matrix.diagonal_apply_ne _ hij]
  have heigsq :
      Multiset.map (fun i => hH.eigenvalues i ^ 2) Finset.univ.val =
        Multiset.map hblock.eigenvalues Finset.univ.val := by
    apply eigenvalues_multiset_unique hblock hH.eigenvectorUnitary.2
    rw [← hermDilation_sq B]
    exact hsqdiag
  have hblocks := eigenvalues_fromBlocks_diagonal_multiset hBB hBtB
  have hleft : Multiset.map hblock.eigenvalues Finset.univ.val =
      Multiset.map hBB.eigenvalues Finset.univ.val +
        Multiset.map hBtB.eigenvalues Finset.univ.val := by
    simpa [hblock] using hblocks
  have hBstar := singularValues_sq_multiset_eq Bᴴ
  have hB := singularValues_sq_multiset_eq B
  rw [heigsq, hleft]
  congr 1
  · simpa [hBB] using hBstar.symm
  · simpa [hBtB] using hB.symm

private lemma count_map_sq_of_nonneg_signed (s : Multiset ℝ) (hs : ∀ y ∈ s, 0 ≤ y)
    {x : ℝ} (hx : 0 < x) :
    (s.map fun y => y ^ 2).count (x ^ 2) = s.count x := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have ha : 0 ≤ a := hs a (Multiset.mem_cons_self a s)
      have hs' : ∀ y ∈ s, 0 ≤ y := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
      have heq : x ^ 2 = a ^ 2 ↔ x = a := by
        constructor
        · intro h
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
          · exact h'
          · nlinarith
        · rintro rfl
          rfl
      rw [Multiset.map_cons, Multiset.count_cons, Multiset.count_cons, ih hs']
      by_cases hxa : x = a
      · subst a
        simp
      · have hsqa : x ^ 2 ≠ a ^ 2 := fun h => hxa (heq.mp h)
        simp [hxa, hsqa]

private lemma count_map_sq_of_pos_signed (s : Multiset ℝ) {x : ℝ} (hx : 0 < x) :
    (s.map fun y => y ^ 2).count (x ^ 2) = s.count x + s.count (-x) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.count_cons, Multiset.count_cons,
        Multiset.count_cons, ih]
      by_cases hax : a = x
      · subst a
        have hne : -x ≠ x := by linarith
        simp [hne]
        omega
      · by_cases han : a = -x
        · subst a
          have hne : x ≠ -x := by linarith
          simp [hne]
          omega
        · have hxa : x ≠ a := fun h => hax h.symm
          have hna : -x ≠ a := fun h => han h.symm
          have hsqa : x ^ 2 ≠ a ^ 2 := by
            intro h
            rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
            · exact hxa h'
            · exact hna (by linarith)
          simp [hxa, hna, hsqa]

private theorem singularValues_count_eq_conjTranspose_signed
    (B : Matrix m n ℂ) {x : ℝ} (hx : 0 < x) :
    (Multiset.map (singularValues B) Finset.univ.val).count x =
      (Multiset.map (singularValues Bᴴ) Finset.univ.val).count x := by
  classical
  let hBB : (B * Bᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self B
  let hBtB : (Bᴴ * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self B
  have hpoly := Matrix.charpoly_mul_comm' B Bᴴ
  have hroots := congrArg Polynomial.roots hpoly
  rw [Polynomial.roots_mul
      (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (B * Bᴴ).charpoly_monic.ne_zero),
    Polynomial.roots_mul
      (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Bᴴ * B).charpoly_monic.ne_zero),
    Polynomial.roots_X_pow, Polynomial.roots_X_pow,
    hBB.roots_charpoly_eq_eigenvalues, hBtB.roots_charpoly_eq_eigenvalues] at hroots
  have hcount := congrArg (fun s : Multiset ℂ => s.count ((x : ℂ) ^ 2)) hroots
  have hxc : ((x : ℂ) ^ 2) ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hx.ne')
  have hprodC :
      (Multiset.map (RCLike.ofReal ∘ hBB.eigenvalues) Finset.univ.val).count
          ((x : ℂ) ^ 2) =
        (Multiset.map (RCLike.ofReal ∘ hBtB.eigenvalues) Finset.univ.val).count
          ((x : ℂ) ^ 2) := by
    simpa [Multiset.count_add, hxc] using hcount
  rw [show Multiset.map (RCLike.ofReal ∘ hBB.eigenvalues) Finset.univ.val =
      Multiset.map RCLike.ofReal (Multiset.map hBB.eigenvalues Finset.univ.val) by
        rw [Multiset.map_map],
    show Multiset.map (RCLike.ofReal ∘ hBtB.eigenvalues) Finset.univ.val =
      Multiset.map RCLike.ofReal (Multiset.map hBtB.eigenvalues Finset.univ.val) by
        rw [Multiset.map_map]] at hprodC
  rw [show ((x : ℂ) ^ 2) = RCLike.ofReal (x ^ 2) by push_cast; rfl] at hprodC
  rw [Multiset.count_map_eq_count' _ _ RCLike.ofReal_injective,
    Multiset.count_map_eq_count' _ _ RCLike.ofReal_injective] at hprodC
  have hsqB := congrArg (fun s : Multiset ℝ => s.count (x ^ 2))
    (singularValues_sq_multiset_eq B)
  have hsqBt := congrArg (fun s : Multiset ℝ => s.count (x ^ 2))
    (singularValues_sq_multiset_eq Bᴴ)
  have hmapB : Multiset.map (fun i => singularValues B i ^ 2) Finset.univ.val =
      Multiset.map (fun y => y ^ 2)
        (Multiset.map (singularValues B) Finset.univ.val) := by
    rw [Multiset.map_map]
    rfl
  have hmapBt : Multiset.map (fun i => singularValues Bᴴ i ^ 2) Finset.univ.val =
      Multiset.map (fun y => y ^ 2)
        (Multiset.map (singularValues Bᴴ) Finset.univ.val) := by
    rw [Multiset.map_map]
    rfl
  rw [hmapB, count_map_sq_of_nonneg_signed _
      (fun y hy => by
        obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hy
        exact singularValues_nonneg B i) hx] at hsqB
  rw [hmapBt, count_map_sq_of_nonneg_signed _
      (fun y hy => by
        obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hy
        exact singularValues_nonneg Bᴴ i) hx] at hsqBt
  have hsqB' :
      (Multiset.map (singularValues B) Finset.univ.val).count x =
        (Multiset.map hBtB.eigenvalues Finset.univ.val).count (x ^ 2) := by
    simpa [hBtB] using hsqB
  have hsqBt' :
      (Multiset.map (singularValues Bᴴ) Finset.univ.val).count x =
        (Multiset.map hBB.eigenvalues Finset.univ.val).count (x ^ 2) := by
    simpa [hBB] using hsqBt
  exact hsqB'.trans (hprodC.symm.trans hsqBt'.symm)

private theorem hermDilation_eigenvalues_neg_signed (B : Matrix m n ℂ) :
    Multiset.map (isHermitian_hermDilation B).eigenvalues Finset.univ.val =
      Multiset.map (fun i => -(isHermitian_hermDilation B).eigenvalues i)
        Finset.univ.val := by
  classical
  let H := hermDilation B
  let hH := isHermitian_hermDilation B
  let J : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
    Matrix.fromBlocks (1 : Matrix m m ℂ) 0 0 (-1 : Matrix n n ℂ)
  have hJJ : J * J = 1 := by
    dsimp [J]
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  have hJHJ : J * H * J = -H := by
    dsimp [J, H, hermDilation]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    rw [show -(Matrix.fromBlocks 0 B Bᴴ 0) =
      Matrix.fromBlocks (-0) (-B) (-Bᴴ) (-0) from by rw [Matrix.fromBlocks_neg]]
    simp
  let Ju : (Matrix (m ⊕ n) (m ⊕ n) ℂ)ˣ := ⟨J, J, hJJ, hJJ⟩
  have hchar0 := Matrix.charpoly_units_conj Ju H
  have hchar : (-H).charpoly = H.charpoly := by
    have hcoe : (↑Ju : Matrix (m ⊕ n) (m ⊕ n) ℂ) = J := rfl
    have hinv : J⁻¹ = J := Matrix.inv_eq_right_inv hJJ
    rw [hcoe, hinv, hJHJ] at hchar0
    exact hchar0
  let hneg : (-H).IsHermitian := hH.neg
  have hroots := congrArg Polynomial.roots hchar
  rw [hneg.roots_charpoly_eq_eigenvalues, hH.roots_charpoly_eq_eigenvalues] at hroots
  have heigNeg :
      Multiset.map hneg.eigenvalues Finset.univ.val =
        Multiset.map hH.eigenvalues Finset.univ.val := by
    apply Multiset.map_injective (RCLike.ofReal_injective :
      Function.Injective (RCLike.ofReal : ℝ → ℂ))
    simpa only [Multiset.map_map] using hroots
  have hnegdiag : -H =
      (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ) *
        diagonal (RCLike.ofReal ∘ fun i => -hH.eigenvalues i) *
        (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ)ᴴ := by
    calc
      -H = -((hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ) *
          diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
          (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ)ᴴ) := by
            rw [← spectral_decomposition hH]
      _ = (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ) *
          (-diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *
          (hH.eigenvectorUnitary : Matrix (m ⊕ n) (m ⊕ n) ℂ)ᴴ := by
            rw [Matrix.mul_neg, Matrix.neg_mul]
      _ = _ := by
        congr 2
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Function.comp_apply]
        · simp [Matrix.diagonal_apply_ne _ hij]
  have hnegvals :
      Multiset.map (fun i => -hH.eigenvalues i) Finset.univ.val =
        Multiset.map hneg.eigenvalues Finset.univ.val :=
    eigenvalues_multiset_unique hneg hH.eigenvectorUnitary.2 hnegdiag
  exact heigNeg.symm.trans hnegvals.symm

private lemma count_map_sq_zero_signed (s : Multiset ℝ) :
    (s.map fun y => y ^ 2).count 0 = s.count 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.count_cons, Multiset.count_cons, ih]
      by_cases ha : a = 0
      · subst a
        simp
      · have ha2 : a ^ 2 ≠ 0 := pow_ne_zero _ ha
        have ha20 : 0 ≠ a ^ 2 := Ne.symm ha2
        have ha0 : 0 ≠ a := Ne.symm ha
        simp [ha20, ha0]

/-- **Book §2.1.16, full signed spectrum:** the eigenvalues of `H(B)`, including
multiplicity and surplus zero eigenvalues, are the singular values of `B` together
with the negatives of the singular values of `Bᴴ`.  This sharpens
`hermDilation_sq_eigenvalues_multiset` from squared eigenvalues to the signed
spectrum and subsumes the spectral content behind `l2_opNorm_hermDilation` and
`lambdaMax_hermDilation`. -/
theorem hermDilation_eigenvalues_multiset (B : Matrix m n ℂ) :
    Multiset.map (isHermitian_hermDilation B).eigenvalues Finset.univ.val =
      Multiset.map (singularValues B) Finset.univ.val +
        Multiset.map (fun i => - singularValues Bᴴ i) Finset.univ.val := by
  classical
  let M := Multiset.map (isHermitian_hermDilation B).eigenvalues Finset.univ.val
  let P := Multiset.map (singularValues B) Finset.univ.val
  let Q := Multiset.map (singularValues Bᴴ) Finset.univ.val
  have hMnonnegSq := hermDilation_sq_eigenvalues_multiset B
  have hsq : M.map (fun y => y ^ 2) =
      Q.map (fun y => y ^ 2) + P.map (fun y => y ^ 2) := by
    simpa only [M, P, Q, Multiset.map_map, Function.comp_apply] using hMnonnegSq
  have hsym0 := hermDilation_eigenvalues_neg_signed B
  have hsym : M = M.map (fun y => -y) := by
    simpa only [M, Multiset.map_map, Function.comp_apply] using hsym0
  have hPnonneg : ∀ y ∈ P, 0 ≤ y := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hy
    exact singularValues_nonneg B i
  have hQnonneg : ∀ y ∈ Q, 0 ≤ y := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hy
    exact singularValues_nonneg Bᴴ i
  have hpos : ∀ {x : ℝ}, 0 < x → M.count x = P.count x := by
    intro x hx
    have hsquared := congrArg (fun s : Multiset ℝ => s.count (x ^ 2)) hsq
    rw [count_map_sq_of_pos_signed M hx, Multiset.count_add,
      count_map_sq_of_nonneg_signed Q hQnonneg hx,
      count_map_sq_of_nonneg_signed P hPnonneg hx] at hsquared
    have hMsym := congrArg (fun s : Multiset ℝ => s.count x) hsym
    have hnegcount : (M.map fun y => -y).count x = M.count (-x) := by
      calc
        (M.map fun y => -y).count x = (M.map fun y => -y).count (-(-x)) := by rw [neg_neg]
        _ = M.count (-x) :=
          Multiset.count_map_eq_count' (fun y : ℝ => -y) M neg_injective (-x)
    rw [hnegcount] at hMsym
    have hPQ := singularValues_count_eq_conjTranspose_signed B hx
    change P.count x = Q.count x at hPQ
    omega
  change M = P + Multiset.map (fun i => -singularValues Bᴴ i) Finset.univ.val
  apply Multiset.ext.mpr
  intro x
  have hnegQ :
      (Multiset.map (fun i => -singularValues Bᴴ i) Finset.univ.val).count x =
        Q.count (-x) := by
    have hmap : Multiset.map (fun i => -singularValues Bᴴ i) Finset.univ.val =
        Q.map (fun y => -y) := by
      simp only [Q, Multiset.map_map, Function.comp_apply]
    rw [hmap]
    calc
      (Q.map fun y => -y).count x = (Q.map fun y => -y).count (-(-x)) := by rw [neg_neg]
      _ = Q.count (-x) :=
        Multiset.count_map_eq_count' (fun y : ℝ => -y) Q neg_injective (-x)
  rw [Multiset.count_add, hnegQ]
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hmx := congrArg (fun s : Multiset ℝ => s.count x) hsym
    have hmneg : (M.map fun y => -y).count x = M.count (-x) := by
      calc
        (M.map fun y => -y).count x = (M.map fun y => -y).count (-(-x)) := by rw [neg_neg]
        _ = M.count (-x) :=
          Multiset.count_map_eq_count' (fun y : ℝ => -y) M neg_injective (-x)
    rw [hmneg] at hmx
    have hpzero : P.count x = 0 := Multiset.count_eq_zero_of_notMem fun hmem => by
      exact (not_le_of_gt hx) (hPnonneg x hmem)
    have hpq := singularValues_count_eq_conjTranspose_signed B (neg_pos.mpr hx)
    change P.count (-x) = Q.count (-x) at hpq
    rw [hpzero, zero_add, ← hpq, ← hpos (neg_pos.mpr hx), ← hmx]
  · have hsquared := congrArg (fun s : Multiset ℝ => s.count 0) hsq
    rw [count_map_sq_zero_signed M, Multiset.count_add,
      count_map_sq_zero_signed Q, count_map_sq_zero_signed P] at hsquared
    simpa [M, P, Q, add_comm] using hsquared
  · have hqzero : Q.count (-x) = 0 := Multiset.count_eq_zero_of_notMem fun hmem => by
      have := hQnonneg (-x) hmem
      linarith
    rw [hqzero, add_zero, hpos hx]

/-- **Book §2.1.16, p. 25**: "As a consequence, `‖H(B)‖ = ‖B‖`." Implicit source
declaration (consequence of (2.1.27) and the block-diagonal norm identity).

**Author note.** See `hermDilation_eigenvalues_multiset` for the stronger full
signed-spectrum statement with multiplicities. -/
theorem l2_opNorm_hermDilation (B : Matrix m n ℂ) : ‖hermDilation B‖ = ‖B‖ := by
  have h1 : ‖hermDilation B * (hermDilation B)ᴴ‖ = ‖hermDilation B‖ ^ 2 :=
    l2_opNorm_sq_mul_conjTranspose_self _
  rw [(isHermitian_hermDilation B), hermDilation_sq,
    l2_opNorm_fromBlocks_diagonal, l2_opNorm_sq_mul_conjTranspose_self,
    l2_opNorm_sq_conjTranspose_mul_self, max_self] at h1
  have h2 := norm_nonneg (hermDilation B)
  have h3 := norm_nonneg B
  nlinarith

/-- Lean implementation helper: `λ_max` respects propositional equality of the
underlying matrices. -/
lemma lambdaMax_congr {A B : Matrix m m ℂ} (h : A = B) (hA : A.IsHermitian)
    (hB : B.IsHermitian) : lambdaMax hA = lambdaMax hB := by
  subst h
  rfl

/-- **Book eq. (2.1.28)** (§2.1.16):
`λ_max(H(B)) = ‖H(B)‖ = ‖B‖` — "We will invoke [this] identity repeatedly."
Explicit (unnumbered) source statement.

**Author note.** See `hermDilation_eigenvalues_multiset` for the stronger full
signed-spectrum statement with multiplicities. -/
theorem lambdaMax_hermDilation (B : Matrix m n ℂ) :
    lambdaMax (isHermitian_hermDilation B) = ‖B‖ := by
  -- the sign-flip unitary J = diag(I, −I)
  have hJconj : (Matrix.fromBlocks (1 : Matrix m m ℂ) 0 0 (-1 : Matrix n n ℂ))ᴴ =
      Matrix.fromBlocks 1 0 0 (-1) := by
    rw [Matrix.fromBlocks_conjTranspose]
    simp
  have hJmem : (Matrix.fromBlocks (1 : Matrix m m ℂ) 0 0 (-1 : Matrix n n ℂ)) ∈
      Matrix.unitaryGroup (m ⊕ n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, hJconj,
      Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  have hJHJ : Matrix.fromBlocks (1 : Matrix m m ℂ) 0 0 (-1 : Matrix n n ℂ) *
      hermDilation B *
      (Matrix.fromBlocks (1 : Matrix m m ℂ) 0 0 (-1 : Matrix n n ℂ))ᴴ =
      -(hermDilation B) := by
    rw [hJconj, hermDilation, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    rw [show -(Matrix.fromBlocks 0 B Bᴴ 0) =
      Matrix.fromBlocks (-0) (-B) (-Bᴴ) (-0) from by rw [Matrix.fromBlocks_neg]]
    simp
  have hB' : ((Matrix.fromBlocks (1 : Matrix m m ℂ) 0 0 (-1 : Matrix n n ℂ)) *
      hermDilation B *
      (Matrix.fromBlocks (1 : Matrix m m ℂ) 0 0 (-1 : Matrix n n ℂ))ᴴ).IsHermitian := by
    rw [hJHJ]
    exact (isHermitian_hermDilation B).neg
  have hconj := lambdaMax_unitary_conj hJmem (isHermitian_hermDilation B) hB'
  have hneg : lambdaMax hB' = lambdaMax (isHermitian_hermDilation B).neg :=
    lambdaMax_congr hJHJ hB' (isHermitian_hermDilation B).neg
  have hsym : -(lambdaMin (isHermitian_hermDilation B)) =
      lambdaMax (isHermitian_hermDilation B) := by
    rw [← lambdaMax_neg (isHermitian_hermDilation B), ← hneg, hconj]
  have hnorm := l2_opNorm_eq_max_lambda (isHermitian_hermDilation B)
  rw [hsym, max_self] at hnorm
  rw [← hnorm]
  exact l2_opNorm_hermDilation B

end MatrixConcentration


set_option linter.unusedSectionVars false

/-!
# Probability with matrices: expectation and independence (Tropp §2.2.1–§2.2.5)

The book's standing regularity convention (§2.2.1: "all random variables are
sufficiently regular … valid if we assume that all random variables are bounded") is
encoded by explicit `MIntegrable`/`Integrable` hypotheses on each statement.

* `expectation` — §2.2.4: the entrywise expectation `(𝔼Z)_{jk} = 𝔼(Z_{jk})` of a random
  matrix (the book's definition, verbatim);
* `MIntegrable` — Lean encoding of the standing regularity convention;
* `expectation_const_mul`, `expectation_mul_const` — §2.2.4: `𝔼(BZ) = B(𝔼Z)`,
  `𝔼(ZB) = (𝔼Z)B`;
* `expectation_mul_of_indepFun` — §2.2.4: "the product rule for the expectation of
  independent random variables extends to matrices: `𝔼(SZ) = (𝔼S)(𝔼Z)`";
* `markov_inequality` — book eq. (2.2.1);
* `iIndepFun_iff_book` — §2.2.3: the book's definition of independence of a finite
  sequence of random matrices (product formula over all Borel sets) is equivalent to
  Mathlib's `iIndepFun` (Mathlib correspondence);
* `rademacherMeasure`, `IsRademacher`, `IsStdGaussian`, `bernoulliMeasureReal`,
  `IsBernoulli` — §2.2.2 (and §1.6.1 footnote): the named scalar random variables.

Random matrices (§2.2.3) are measurable maps `Ω → Matrix m n ℂ` where the matrix space
carries its (product) Borel σ-algebra — Mathlib's `Measurable` with the `Pi` instances.
-/

namespace MatrixConcentration

open Matrix MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-- Random matrices (book §2.2.3) carry the Borel/product σ-algebra: the `Pi`
σ-algebra on `Matrix m n ℂ = m → n → ℂ`. Lean implementation helper (Mathlib has no
`MeasurableSpace` instance on `Matrix`). -/
noncomputable instance instMeasurableSpaceMatrix : MeasurableSpace (Matrix m n ℂ) :=
  MeasurableSpace.pi

/-- Lean implementation helper: the product σ-algebra on matrices is the Borel
σ-algebra of the (product) topology. -/
instance instBorelSpaceMatrix : BorelSpace (Matrix m n ℂ) := Pi.borelSpace

/-- **Book §2.2.4**: the **expectation of a random matrix**, defined entrywise:
`(𝔼Z)_{jk} = 𝔼(Z_{jk})`. Explicit source declaration. -/
noncomputable def expectation (μ : MeasureTheory.Measure Ω) (Z : Ω → Matrix m n ℂ) :
    Matrix m n ℂ :=
  Matrix.of fun i j => ∫ ω, Z ω i j ∂μ

@[simp] lemma expectation_apply (Z : Ω → Matrix m n ℂ) (i : m) (j : n) :
    expectation μ Z i j = ∫ ω, Z ω i j ∂μ := rfl

/-- Lean encoding of the standing regularity convention of §2.2.1: a random matrix is
integrable when each entry is. Lean implementation helper. -/
def MIntegrable (Z : Ω → Matrix m n ℂ) (μ : MeasureTheory.Measure Ω) : Prop :=
  ∀ i j, MeasureTheory.Integrable (fun ω => Z ω i j) μ

/-- Lean implementation helper: entry evaluation is measurable. -/
lemma measurable_entry (i : m) (j : n) : Measurable fun M : Matrix m n ℂ => M i j := by
  have h1 : Measurable fun M : Matrix m n ℂ => M i :=
    measurable_pi_apply (X := fun _ : m => n → ℂ) i
  exact (measurable_pi_apply j).comp h1

/-- Lean implementation helper: bounded measurable random matrices are integrable
(the book's standing convention: "valid if we assume that all random variables are
bounded"). -/
lemma MIntegrable.of_bound [MeasureTheory.IsFiniteMeasure μ] {Z : Ω → Matrix m n ℂ}
    (hZm : Measurable Z) (C : ℝ) (hC : ∀ᵐ ω ∂μ, ∀ i j, ‖Z ω i j‖ ≤ C) :
    MIntegrable Z μ := fun i j =>
  MeasureTheory.Integrable.of_bound
    (((measurable_entry i j).comp hZm).aestronglyMeasurable) C
    (hC.mono fun ω h => h i j)

/-- Lean implementation helper: the conjugate of an integrable complex random variable
is integrable. -/
lemma integrable_conj {f : Ω → ℂ} (hf : MeasureTheory.Integrable f μ) :
    MeasureTheory.Integrable (fun ω => (starRingEnd ℂ) (f ω)) μ := by
  have h1 : MeasureTheory.AEStronglyMeasurable (fun ω => (starRingEnd ℂ) (f ω)) μ :=
    RCLike.continuous_conj.comp_aestronglyMeasurable hf.1
  refine (MeasureTheory.integrable_norm_iff h1).mp ?_
  simpa [RCLike.norm_conj] using hf.norm

namespace MIntegrable

variable {Y Z : Ω → Matrix m n ℂ}

/-- Lean implementation helper: entrywise matrix integrability is closed under addition. -/
lemma add (hY : MIntegrable Y μ) (hZ : MIntegrable Z μ) :
    MIntegrable (fun ω => Y ω + Z ω) μ := fun i j => (hY i j).add (hZ i j)

/-- Lean implementation helper: entrywise matrix integrability is closed under negation. -/
lemma neg (hZ : MIntegrable Z μ) : MIntegrable (fun ω => -(Z ω)) μ := fun i j =>
  (hZ i j).neg

/-- Lean implementation helper: entrywise matrix integrability is closed under subtraction. -/
lemma sub (hY : MIntegrable Y μ) (hZ : MIntegrable Z μ) :
    MIntegrable (fun ω => Y ω - Z ω) μ := fun i j => (hY i j).sub (hZ i j)

/-- Lean implementation helper: entrywise matrix integrability is closed under complex scaling. -/
lemma smul_complex (c : ℂ) (hZ : MIntegrable Z μ) :
    MIntegrable (fun ω => c • Z ω) μ := fun i j => by
  simpa [Matrix.smul_apply, smul_eq_mul] using (hZ i j).const_mul c

/-- Lean implementation helper: entrywise matrix integrability is closed under conjugate transpose. -/
lemma conjTranspose (hZ : MIntegrable Z μ) :
    MIntegrable (fun ω => (Z ω)ᴴ) μ := fun i j => by
  simpa [Matrix.conjTranspose_apply, RCLike.star_def] using integrable_conj (hZ j i)

/-- Lean implementation helper: constant matrices are integrable over finite measures. -/
lemma const [MeasureTheory.IsFiniteMeasure μ] (B : Matrix m n ℂ) :
    MIntegrable (fun _ => B) μ := fun _ _ => MeasureTheory.integrable_const _

/-- Lean implementation helper: left multiplication preserves entrywise matrix integrability. -/
lemma const_mul (hZ : MIntegrable Z μ) (B : Matrix l m ℂ) :
    MIntegrable (fun ω => B * Z ω) μ := fun i j => by
  have h : (fun ω => (B * Z ω) i j) = fun ω => ∑ k, B i k * Z ω k j := by
    funext ω
    exact Matrix.mul_apply
  rw [h]
  exact MeasureTheory.integrable_finsetSum _ fun k _ => (hZ k j).const_mul _

/-- Lean implementation helper: right multiplication preserves entrywise matrix integrability. -/
lemma mul_const (hZ : MIntegrable Z μ) (B : Matrix n p ℂ) :
    MIntegrable (fun ω => Z ω * B) μ := fun i j => by
  have h : (fun ω => (Z ω * B) i j) = fun ω => ∑ k, Z ω i k * B k j := by
    funext ω
    exact Matrix.mul_apply
  rw [h]
  exact MeasureTheory.integrable_finsetSum _ fun k _ => (hZ i k).mul_const _

end MIntegrable

section Linearity

variable {Y Z : Ω → Matrix m n ℂ}

/-- **Book §2.2.4**: "expectation commutes with linear and real-linear maps" — additivity.
Explicit (prose) source statement. -/
theorem expectation_add (hY : MIntegrable Y μ) (hZ : MIntegrable Z μ) :
    expectation μ (fun ω => Y ω + Z ω) = expectation μ Y + expectation μ Z := by
  ext i j
  simpa using MeasureTheory.integral_add (hY i j) (hZ i j)

/-- **Book §2.2.4**: expectation commutes with negation. -/
theorem expectation_neg (Z : Ω → Matrix m n ℂ) :
    expectation μ (fun ω => -(Z ω)) = -(expectation μ Z) := by
  ext i j
  simpa using MeasureTheory.integral_neg _

/-- **Book §2.2.4**: expectation commutes with subtraction. -/
theorem expectation_sub (hY : MIntegrable Y μ) (hZ : MIntegrable Z μ) :
    expectation μ (fun ω => Y ω - Z ω) = expectation μ Y - expectation μ Z := by
  ext i j
  simpa using MeasureTheory.integral_sub (hY i j) (hZ i j)

/-- **Book §2.2.4**: expectation commutes with complex scalar multiplication. -/
theorem expectation_smul_complex (c : ℂ) (Z : Ω → Matrix m n ℂ) :
    expectation μ (fun ω => c • Z ω) = c • expectation μ Z := by
  ext i j
  simpa [Matrix.smul_apply, smul_eq_mul] using
    MeasureTheory.integral_const_mul c (fun ω => Z ω i j)

/-- **Book §2.2.4 (used implicitly throughout §2.2)**: expectation commutes with the
conjugate transpose. Implicit source declaration. -/
theorem expectation_conjTranspose (Z : Ω → Matrix m n ℂ) :
    expectation μ (fun ω => (Z ω)ᴴ) = (expectation μ Z)ᴴ := by
  ext i j
  simp only [expectation_apply, Matrix.conjTranspose_apply]
  exact integral_conj

/-- **Book §2.2.4**: expectation of a constant matrix. Implicit source declaration. -/
theorem expectation_const [MeasureTheory.IsProbabilityMeasure μ] (B : Matrix m n ℂ) :
    expectation μ (fun _ => B) = B := by
  ext i j
  simp

/-- **Book §2.2.4 (used for §2.2.6)**: the trace commutes with expectation. Lean
implementation helper. -/
theorem expectation_trace {Z : Ω → Matrix m m ℂ} (hZ : MIntegrable Z μ) :
    ∫ ω, (Z ω).trace ∂μ = (expectation μ Z).trace := by
  have h : ∀ ω, (Z ω).trace = ∑ i, Z ω i i := fun ω => rfl
  simp only [h]
  rw [MeasureTheory.integral_finsetSum _ fun i _ => hZ i i]
  rfl

/-- **Book §2.2.4**: "expectation commutes with multiplication by a fixed matrix:
`𝔼(BZ) = B(𝔼Z)`." Explicit (unnumbered) source statement. -/
theorem expectation_const_mul (hZ : MIntegrable Z μ) (B : Matrix l m ℂ) :
    expectation μ (fun ω => B * Z ω) = B * expectation μ Z := by
  ext i j
  rw [expectation_apply, Matrix.mul_apply]
  have h : (fun ω => (B * Z ω) i j) = fun ω => ∑ k, B i k * Z ω k j := by
    funext ω
    exact Matrix.mul_apply
  rw [h, MeasureTheory.integral_finsetSum _ fun k _ => (hZ k j).const_mul _]
  exact Finset.sum_congr rfl fun k _ => MeasureTheory.integral_const_mul _ _

/-- **Book §2.2.4**: "`𝔼(ZB) = (𝔼Z)B`." Explicit (unnumbered) source statement. -/
theorem expectation_mul_const (hZ : MIntegrable Z μ) (B : Matrix n p ℂ) :
    expectation μ (fun ω => Z ω * B) = expectation μ Z * B := by
  ext i j
  rw [expectation_apply, Matrix.mul_apply]
  have h : (fun ω => (Z ω * B) i j) = fun ω => ∑ k, Z ω i k * B k j := by
    funext ω
    exact Matrix.mul_apply
  rw [h, MeasureTheory.integral_finsetSum _ fun k _ => (hZ i k).mul_const _]
  exact Finset.sum_congr rfl fun k _ => MeasureTheory.integral_mul_const _ _

end Linearity

/-- **Book §2.2.4**: "the product rule for the expectation of independent random variables
extends to matrices: `𝔼(SZ) = (𝔼S)(𝔼Z)` when `S` and `Z` are independent."
Explicit (unnumbered) source statement. -/
theorem expectation_mul_of_indepFun {S : Ω → Matrix l m ℂ} {Z : Ω → Matrix m n ℂ}
    (h : ProbabilityTheory.IndepFun S Z μ) (hSm : Measurable S) (hZm : Measurable Z)
    (hS : MIntegrable S μ) (hZ : MIntegrable Z μ) :
    expectation μ (fun ω => S ω * Z ω) = expectation μ S * expectation μ Z := by
  ext i j
  rw [expectation_apply, Matrix.mul_apply]
  have hmul : (fun ω => (S ω * Z ω) i j) = fun ω => ∑ k, S ω i k * Z ω k j := by
    funext ω
    exact Matrix.mul_apply
  have hind : ∀ k : m, ProbabilityTheory.IndepFun
      (fun ω => S ω i k) (fun ω => Z ω k j) μ := fun k =>
    h.comp (measurable_entry i k) (measurable_entry k j)
  rw [hmul, MeasureTheory.integral_finsetSum (f := fun k ω => S ω i k * Z ω k j)
    Finset.univ (fun k _ => (hind k).integrable_mul (hS i k) (hZ k j))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := (hind k).integral_mul_eq_mul_integral
    ((measurable_entry i k).comp hSm).aestronglyMeasurable
    ((measurable_entry k j).comp hZm).aestronglyMeasurable
  simpa [Pi.mul_apply] using this

/-- **Book eq. (2.2.1) (§2.2.5)**: **Markov's inequality** — a nonnegative real
random variable `X` obeys `ℙ{X ≥ t} ≤ 𝔼X/t` for `t > 0`. Explicit (unnumbered) source
statement; Mathlib correspondence (`mul_meas_ge_le_integral_of_nonneg`).

Author note: Lean only requires nonnegativity almost everywhere, which is stronger
than the source's pointwise random-variable convention. -/
theorem markov_inequality {X : Ω → ℝ} (h0 : 0 ≤ᵐ[μ] X)
    (hX : MeasureTheory.Integrable X μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ X ω} ≤ (∫ ω, X ω ∂μ) / t := by
  have h := MeasureTheory.mul_meas_ge_le_integral_of_nonneg h0 hX t
  rw [le_div_iff₀ ht]
  linarith

/-- **Book §2.2.3**: "A finite sequence `{Zₖ}` of random matrices is *independent* when
`ℙ{Zₖ ∈ Fₖ for each k} = ∏ₖ ℙ{Zₖ ∈ Fₖ}` for every collection `{Fₖ}` of Borel subsets."
Mathlib correspondence lemma: this coincides with Mathlib's `iIndepFun`. -/
theorem iIndepFun_iff_book {ι : Type*} [Fintype ι]
    [MeasureTheory.IsProbabilityMeasure μ] {Z : ι → Ω → Matrix m n ℂ}
    (hZ : ∀ k, Measurable (Z k)) :
    ProbabilityTheory.iIndepFun Z μ ↔
      ∀ F : ι → Set (Matrix m n ℂ), (∀ k, MeasurableSet (F k)) →
        μ (⋂ k, Z k ⁻¹' F k) = ∏ k, μ (Z k ⁻¹' F k) := by
  constructor
  · intro hind F hF
    have h := ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hind
      Finset.univ (sets := F) (fun i _ => hF i)
    simpa using h
  · intro hbook
    rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    classical
    have h1 := hbook (fun k => if k ∈ S then sets k else Set.univ) (fun k => by
      by_cases hk : k ∈ S
      · simpa [hk] using hsets k hk
      · simp [hk])
    have h2 : (⋂ k, Z k ⁻¹' (if k ∈ S then sets k else Set.univ)) =
        ⋂ i ∈ S, Z i ⁻¹' sets i := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro h i hi
        have := h i
        rwa [if_pos hi] at this
      · intro h i
        by_cases hi : i ∈ S
        · rw [if_pos hi]
          exact h i hi
        · rw [if_neg hi]
          exact Set.mem_univ _
    have h3 : (∏ k, μ (Z k ⁻¹' (if k ∈ S then sets k else Set.univ))) =
        ∏ i ∈ S, μ (Z i ⁻¹' sets i) := by
      rw [show (∏ i ∈ S, μ (Z i ⁻¹' sets i)) =
        ∏ i ∈ S, μ (Z i ⁻¹' (if i ∈ S then sets i else Set.univ)) from
        Finset.prod_congr rfl fun k hk => by rw [if_pos hk]]
      exact (Finset.prod_subset (Finset.subset_univ S) fun k _ hk => by
        rw [if_neg hk]
        simp).symm
    rw [h2, h3] at h1
    exact h1

section Distributions

/-- **Book §2.2.2 / §1.6.1 footnote**: "A *Rademacher random variable* takes the two values
±1 with equal probability" — its law. Implicit source declaration. -/
noncomputable def rademacherMeasure : MeasureTheory.Measure ℝ :=
  (2⁻¹ : ENNReal) • MeasureTheory.Measure.dirac 1 +
    (2⁻¹ : ENNReal) • MeasureTheory.Measure.dirac (-1)

instance : MeasureTheory.IsProbabilityMeasure rademacherMeasure := by
  constructor
  rw [rademacherMeasure]
  simp [ENNReal.inv_two_add_inv_two]

/-- **Book §2.2.2**: a random variable is Rademacher when its law is `rademacherMeasure`.
Implicit source declaration. -/
def IsRademacher (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω) : Prop :=
  MeasureTheory.Measure.map X μ = rademacherMeasure

/-- Sanity check: a Rademacher variable has mean zero. Lean implementation helper. -/
lemma rademacherMeasure_integral_id : ∫ x, x ∂rademacherMeasure = 0 := by
  rw [rademacherMeasure]
  rw [MeasureTheory.integral_add_measure]
  · rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure,
      MeasureTheory.integral_dirac, MeasureTheory.integral_dirac]
    norm_num
  · exact (MeasureTheory.integrable_dirac enorm_lt_top).smul_measure (by norm_num)
  · exact (MeasureTheory.integrable_dirac enorm_lt_top).smul_measure (by norm_num)

/-- **Book §2.2.2**: "We reserve the letter γ for a NORMAL(0,1) random variable" — a random
variable is standard normal when its law is the standard Gaussian. Implicit source
declaration. -/
def IsStdGaussian (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω) : Prop :=
  MeasureTheory.Measure.map X μ = ProbabilityTheory.gaussianReal 0 1

/-- **Book §2.2.2**: the law of a BERNOULLI(p) random variable (value 1 with probability
`p`, value 0 with probability `1 − p`). Implicit source declaration. -/
noncomputable def bernoulliMeasureReal (p : ℝ) : MeasureTheory.Measure ℝ :=
  ENNReal.ofReal p • MeasureTheory.Measure.dirac 1 +
    ENNReal.ofReal (1 - p) • MeasureTheory.Measure.dirac 0

/-- Lean implementation helper: the Bernoulli law has total mass one for `p ∈ [0,1]`. -/
lemma isProbabilityMeasure_bernoulliMeasureReal {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    MeasureTheory.IsProbabilityMeasure (bernoulliMeasureReal p) := by
  constructor
  rw [bernoulliMeasureReal]
  simp only [MeasureTheory.Measure.coe_add, MeasureTheory.Measure.coe_smul,
    Pi.add_apply, Pi.smul_apply, MeasureTheory.measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp.1 (by linarith [hp.2])]
  norm_num

/-- **Book §2.2.2**: a random variable is BERNOULLI(p) when its law is
`bernoulliMeasureReal p`. Implicit source declaration. -/
def IsBernoulli (p : ℝ) (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω) : Prop :=
  MeasureTheory.Measure.map X μ = bernoulliMeasureReal p

end Distributions

end MatrixConcentration

namespace MatrixConcentration

open Matrix MeasureTheory ProbabilityTheory Finset
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Book §1.6.5, p. 11**: "each summand `Sₖ` is a *symmetric* random variable; that is,
`Sₖ` and `−Sₖ` have the same distribution." Implicit source declaration (used by the
optimality discussion, Chapter 6 §6.1.2). -/
def IsSymmetricRV {E : Type*} [MeasurableSpace E] [Neg E] (X : Ω → E)
    (μ : MeasureTheory.Measure Ω) : Prop :=
  MeasureTheory.Measure.map X μ = MeasureTheory.Measure.map (fun ω => -(X ω)) μ

/-- **Book §1.6.5, p. 11**: the average upper bound `L⋆² = 𝔼 maxₖ ‖Sₖ‖²` for the summands.
Implicit source declaration (used by (1.6.7) and Chapter 6 §6.1.2). -/
noncomputable def maxSummandSq {ι : Type*} (S : ι → Ω → Matrix m n ℂ)
    (μ : MeasureTheory.Measure Ω) : ℝ :=
  ∫ ω, ⨆ k, ‖S k ω‖ ^ 2 ∂μ

/-- Lean implementation helper: measurability of `ω ↦ S(ω)S(ω)*`. -/
lemma measurable_mul_conjTranspose_self {S : Ω → Matrix m n ℂ}
    (hS : Measurable S) : Measurable fun ω => S ω * (S ω)ᴴ := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have h : (fun ω => (S ω * (S ω)ᴴ) i j) =
      fun ω => ∑ l, S ω i l * star (S ω j l) := by
    funext ω
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [Matrix.conjTranspose_apply]
  rw [h]
  exact Finset.measurable_sum _ fun l _ =>
    ((measurable_entry i l).comp hS).mul
      (continuous_star.measurable.comp ((measurable_entry j l).comp hS))

/-- Lean implementation helper: measurability of `ω ↦ S(ω)*S(ω)`. -/
lemma measurable_conjTranspose_mul_self {S : Ω → Matrix m n ℂ}
    (hS : Measurable S) : Measurable fun ω => (S ω)ᴴ * S ω := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have h : (fun ω => ((S ω)ᴴ * S ω) i j) =
      fun ω => ∑ l, star (S ω l i) * S ω l j := by
    funext ω
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [Matrix.conjTranspose_apply]
  rw [h]
  exact Finset.measurable_sum _ fun l _ =>
    (continuous_star.measurable.comp ((measurable_entry l i).comp hS)).mul
      ((measurable_entry l j).comp hS)

end MatrixConcentration


set_option linter.unusedSectionVars false

/-!
# Expectation, the semidefinite order, and Jensen's inequality (Tropp §2.2.5)

* `posSemidef_expectation`, `expectation_loewner_mono` — book §2.2.5: "expectation
  preserves the semidefinite order" (the book derives this from the fact that the psd
  matrices form a convex cone and expectation is a convex combination; here realized on
  the quadratic form, the analytic content of that argument);
* `norm_expectation_le` — book eq. (2.2.2) instantiated at the convex
  function `h = ‖·‖`; this is the instance invoked at §1.6.3 ("This expression depends
  on Jensen's inequality");
* `lambdaMax_expectation_le` — eq. (2.2.2) instantiated at the convex function
  `h = λ_max` (the instance used by Chapter 3).

The book states (2.2.2) as a schema for arbitrary concave/convex `h` under the standing
regularity convention; the statement audit records why these instances exhaust every
later use of (2.2.2) in the book.
-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Lean implementation helper: the sesquilinear form of an expectation is the
expectation of the sesquilinear form. -/
lemma star_dotProduct_expectation {Z : Ω → Matrix m n ℂ} (hZ : MIntegrable Z μ)
    (u : m → ℂ) (v : n → ℂ) :
    star u ⬝ᵥ (expectation μ Z *ᵥ v) = ∫ ω, star u ⬝ᵥ (Z ω *ᵥ v) ∂μ := by
  have hint : ∀ (i : m) (j : n),
      MeasureTheory.Integrable (fun ω => star (u i) * (Z ω i j * v j)) μ :=
    fun i j => ((hZ i j).mul_const (v j)).const_mul (star (u i))
  have h1 : ∀ ω, star u ⬝ᵥ (Z ω *ᵥ v) = ∑ i, ∑ j, star (u i) * (Z ω i j * v j) :=
    fun ω => by
      show (∑ i, star (u i) * ∑ j, Z ω i j * v j) = _
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  have h2 : star u ⬝ᵥ (expectation μ Z *ᵥ v) =
      ∑ i, ∑ j, star (u i) * ((∫ ω, Z ω i j ∂μ) * v j) := by
    show (∑ i, star (u i) * ∑ j, expectation μ Z i j * v j) = _
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]; rfl
  simp only [h1]
  rw [MeasureTheory.integral_finsetSum _ fun i _ =>
    MeasureTheory.integrable_finsetSum _ fun j _ => hint i j, h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]

/-- Lean implementation helper: integrability of the quadratic form. -/
lemma integrable_star_dotProduct {Z : Ω → Matrix m n ℂ} (hZ : MIntegrable Z μ)
    (u : m → ℂ) (v : n → ℂ) :
    MeasureTheory.Integrable (fun ω => star u ⬝ᵥ (Z ω *ᵥ v)) μ := by
  have h1 : ∀ ω, star u ⬝ᵥ (Z ω *ᵥ v) = ∑ i, ∑ j, star (u i) * (Z ω i j * v j) :=
    fun ω => by
      show (∑ i, star (u i) * ∑ j, Z ω i j * v j) = _
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  simp only [h1]
  exact MeasureTheory.integrable_finsetSum _ fun i _ =>
    MeasureTheory.integrable_finsetSum _ fun j _ =>
      ((hZ i j).mul_const (v j)).const_mul (star (u i))

/-- **Book §2.2.5, p. 27**: "the expectation of a random matrix can be viewed as a convex
combination [and the psd matrices form a convex cone]. Therefore, expectation preserves
the semidefinite order" — the psd case: the expectation of an (a.e.) positive-
semidefinite random matrix is positive semidefinite. Explicit (prose) source
statement.

Author note: Lean only requires positive semidefiniteness almost everywhere. -/
theorem posSemidef_expectation {Z : Ω → Matrix n n ℂ} (hZ : MIntegrable Z μ)
    (h : ∀ᵐ ω ∂μ, (Z ω).PosSemidef) : (expectation μ Z).PosSemidef := by
  rw [posSemidef_iff_isHermitian_quadratic]
  constructor
  · show (expectation μ Z)ᴴ = expectation μ Z
    ext i j
    rw [Matrix.conjTranspose_apply, expectation_apply, expectation_apply]
    rw [show star (∫ ω, Z ω j i ∂μ) = ∫ ω, (starRingEnd ℂ) (Z ω j i) ∂μ from
      integral_conj.symm]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h] with ω hω
    calc (starRingEnd ℂ) (Z ω j i) = (Z ω)ᴴ i j := rfl
      _ = Z ω i j := by rw [hω.1]
  · intro u
    rw [star_dotProduct_expectation hZ u u, ← RCLike.re_to_complex,
      ← integral_re (integrable_star_dotProduct hZ u u)]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [h] with ω hω
    exact hω.re_dotProduct_nonneg u

/-- **Book §2.2.5, p. 27**: "expectation preserves the semidefinite order:
`X ≼ Y` implies `𝔼X ≼ 𝔼Y`." Explicit (unnumbered) source statement (a.e. hypothesis,
the measure-theoretic reading).

Author note: the almost-everywhere order hypothesis is stronger than a pointwise
formulation. -/
theorem expectation_loewner_mono {X Y : Ω → Matrix n n ℂ} (hX : MIntegrable X μ)
    (hY : MIntegrable Y μ) (h : ∀ᵐ ω ∂μ, X ω ≤ Y ω) :
    expectation μ X ≤ expectation μ Y := by
  rw [Matrix.le_iff]
  have h1 : expectation μ Y - expectation μ X =
      expectation μ (fun ω => Y ω - X ω) := (expectation_sub hY hX).symm
  rw [h1]
  refine posSemidef_expectation (hY.sub hX) ?_
  filter_upwards [h] with ω hω
  exact Matrix.le_iff.mp hω

/-- **Book eq. (2.2.2)** (§2.2.5), instantiated at the convex function
`h = ‖·‖` (the spectral norm): `‖𝔼Z‖ ≤ 𝔼‖Z‖`. This is the Jensen instance used at
§1.6.3. Explicit source statement (instance of the schema (2.2.2)). -/
theorem norm_expectation_le {Z : Ω → Matrix m n ℂ} (hZ : MIntegrable Z μ)
    (hnorm : MeasureTheory.Integrable (fun ω => ‖Z ω‖) μ) :
    ‖expectation μ Z‖ ≤ ∫ ω, ‖Z ω‖ ∂μ := by
  refine l2_opNorm_le_of_forall_dotProduct _
    (MeasureTheory.integral_nonneg fun ω => norm_nonneg _) fun u v => ?_
  rw [star_dotProduct_expectation hZ u v]
  calc ‖∫ ω, star u ⬝ᵥ (Z ω *ᵥ v) ∂μ‖
      ≤ ∫ ω, ‖star u ⬝ᵥ (Z ω *ᵥ v)‖ ∂μ := MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ‖Z ω‖ * l2norm u * l2norm v ∂μ := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => norm_nonneg _)
          ((hnorm.mul_const (l2norm u)).mul_const (l2norm v)) ?_
        exact Filter.Eventually.of_forall fun ω => norm_dotProduct_mulVec_le (Z ω) u v
    _ = (∫ ω, ‖Z ω‖ ∂μ) * l2norm u * l2norm v := by
        rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]

/-- **Book eq. (2.2.2)** (§2.2.5), instantiated at the convex function
`h = λ_max` (the instance used by Chapter 3): `λ_max(𝔼Y) ≤ 𝔼 λ_max(Y)`. Explicit
source statement (instance of the schema (2.2.2)). -/
theorem lambdaMax_expectation_le [Nonempty n] {Y : Ω → Matrix n n ℂ}
    (hY : MIntegrable Y μ) (hHerm : ∀ ω, (Y ω).IsHermitian)
    (hEHerm : (expectation μ Y).IsHermitian)
    (hint : MeasureTheory.Integrable (fun ω => lambdaMax (hHerm ω)) μ) :
    lambdaMax hEHerm ≤ ∫ ω, lambdaMax (hHerm ω) ∂μ := by
  refine lambdaMax_le_of_forall_rayleigh hEHerm fun u hu => ?_
  have h1 : rayleigh (expectation μ Y) u = ∫ ω, rayleigh (Y ω) u ∂μ := by
    rw [rayleigh, star_dotProduct_expectation hY u u, ← RCLike.re_to_complex,
      ← integral_re (integrable_star_dotProduct hY u u)]
    rfl
  rw [h1]
  exact MeasureTheory.integral_mono (integrable_star_dotProduct hY u u).re hint
    fun ω => rayleigh_le_lambdaMax_of_unit (hHerm ω) hu

/-- **Book eq. (2.2.2)** (§2.2.5), instantiated at the concave function
`h = λ_min`: `𝔼 λ_min(Y) ≤ λ_min(𝔼Y)`. Explicit source statement (instance of the
schema (2.2.2)). -/
theorem expectation_lambdaMin_le [Nonempty n] {Y : Ω → Matrix n n ℂ}
    (hY : MIntegrable Y μ) (hHerm : ∀ ω, (Y ω).IsHermitian)
    (hEHerm : (expectation μ Y).IsHermitian)
    (hint : MeasureTheory.Integrable (fun ω => lambdaMin (hHerm ω)) μ) :
    ∫ ω, lambdaMin (hHerm ω) ∂μ ≤ lambdaMin hEHerm := by
  refine le_lambdaMin_of_forall_rayleigh hEHerm fun u hu => ?_
  have h1 : rayleigh (expectation μ Y) u = ∫ ω, rayleigh (Y ω) u ∂μ := by
    rw [rayleigh, star_dotProduct_expectation hY u u, ← RCLike.re_to_complex,
      ← integral_re (integrable_star_dotProduct hY u u)]
    rfl
  rw [h1]
  exact MeasureTheory.integral_mono hint (integrable_star_dotProduct hY u u).re
    fun ω => lambdaMin_le_rayleigh_of_unit (hHerm ω) hu

end MatrixConcentration


set_option linter.unusedSectionVars false

/-!
# The variance of a random Hermitian matrix (Tropp §2.2.6–§2.2.7)

* `matrixVar` — book eq. (2.2.3): the matrix-valued variance
  `mVar(Y) = 𝔼(Y − 𝔼Y)²`, with the identity `= 𝔼Y² − (𝔼Y)²` (`matrixVar_eq_sub`);
* `posSemidef_matrixVar` — "The matrix `mVar(Y)` is always positive semidefinite"
  (p. 27, implicit claim);
* `matrixVar_apply` — the column-covariance interpretation display of p. 28;
* `varStatHerm` — book eq. (2.2.4): the matrix variance
  statistic `v(Y) = ‖mVar(Y)‖`;
* `varStatHerm_eq_lambdaMax` + `rayleigh_matrixVar` — the variational display of p. 28
  (`v(Y) = sup_{‖u‖=1} 𝔼‖Yu − 𝔼(Yu)‖²`), rendered as: `v(Y)` is the maximum eigenvalue
  of `mVar(Y)`, whose Rayleigh value at a unit `u` is exactly `𝔼‖(Y−𝔼Y)u‖²` (the sup
  over unit vectors is `λ_max` by the Prelude Rayleigh API);
* `matrixVar_sum` — book eq. (2.2.5): additivity of the
  matrix-valued variance over an independent sum (including the vanishing cross terms);
* `varStatHerm_sum` — book eq. (2.2.6);
* `varStatHerm_sum_le`, `sum_varStatHerm_le_card_mul` — p. 28: "the best general
  inequalities … are `v(Y) ≤ Σ v(Xₖ) ≤ d·v(Y)`";
* `varStatHerm_sum_of_identDistrib` — p. 28: "when the matrices are identically
  distributed, the left-hand inequality becomes an identity".
-/

namespace MatrixConcentration

open Matrix MeasureTheory ProbabilityTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section Helpers

/-- Lean implementation helper: expectation of a finite sum. -/
lemma expectation_finsetSum {ι : Type*} (s : Finset ι) {X : ι → Ω → Matrix m n ℂ}
    (hX : ∀ k ∈ s, MIntegrable (X k) μ) :
    expectation μ (fun ω => ∑ k ∈ s, X k ω) = ∑ k ∈ s, expectation μ (X k) := by
  ext i j
  rw [expectation_apply]
  have h1 : ∀ ω, (∑ k ∈ s, X k ω) i j = ∑ k ∈ s, X k ω i j := fun ω => by
    rw [Matrix.sum_apply]
  simp only [h1]
  rw [MeasureTheory.integral_finsetSum _ fun k hk => hX k hk i j, Matrix.sum_apply]
  rfl

/-- Lean implementation helper: `MIntegrable` is closed under finite sums. -/
lemma MIntegrable.finsetSum {ι : Type*} (s : Finset ι) {X : ι → Ω → Matrix m n ℂ}
    (hX : ∀ k ∈ s, MIntegrable (X k) μ) :
    MIntegrable (fun ω => ∑ k ∈ s, X k ω) μ := fun i j => by
  have h1 : ∀ ω, (∑ k ∈ s, X k ω) i j = ∑ k ∈ s, X k ω i j := fun ω => by
    rw [Matrix.sum_apply]
  simp only [h1]
  exact MeasureTheory.integrable_finsetSum _ fun k hk => hX k hk i j

/-- Lean implementation helper: translation by a constant matrix is measurable. -/
lemma measurable_sub_const (C : Matrix m n ℂ) :
    Measurable fun M : Matrix m n ℂ => M - C := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have h1 : (fun M : Matrix m n ℂ => (M - C) i j) =
      fun M : Matrix m n ℂ => M i j - C i j := rfl
  rw [h1]
  exact (measurable_entry i j).sub_const _

/-- Lean implementation helper: the conjugate transpose is measurable. -/
lemma measurable_conjTranspose_map :
    Measurable fun M : Matrix m n ℂ => Mᴴ := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have h1 : (fun M : Matrix m n ℂ => Mᴴ i j) =
      fun M : Matrix m n ℂ => (starRingEnd ℂ) (M j i) := rfl
  rw [h1]
  exact RCLike.continuous_conj.measurable.comp (measurable_entry j i)

/-- Lean implementation helper: a centered random matrix has expectation zero. -/
lemma expectation_centered [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → Matrix m n ℂ} (hX : MIntegrable X μ) :
    expectation μ (fun ω => X ω - expectation μ X) = 0 := by
  rw [expectation_sub hX (MIntegrable.const _), expectation_const, sub_self]

/-- Lean implementation helper: products of independent integrable random matrices are
integrable (entrywise, via `IndepFun.integrable_mul`). -/
lemma MIntegrable.mul_of_indepFun {l : Type*} [Fintype l] [DecidableEq l]
    {S : Ω → Matrix l m ℂ} {Z : Ω → Matrix m n ℂ}
    (h : ProbabilityTheory.IndepFun S Z μ)
    (hS : MIntegrable S μ) (hZ : MIntegrable Z μ) :
    MIntegrable (fun ω => S ω * Z ω) μ := fun i j => by
  have hmul : (fun ω => (S ω * Z ω) i j) = fun ω => ∑ k, S ω i k * Z ω k j := by
    funext ω
    exact Matrix.mul_apply
  rw [hmul]
  refine MeasureTheory.integrable_finsetSum _ fun k _ => ?_
  exact (h.comp (measurable_entry i k) (measurable_entry k j)).integrable_mul
    (hS i k) (hZ k j)

/-- Lean implementation helper: the expectation of an a.e.-Hermitian random matrix is
Hermitian. -/
lemma isHermitian_expectation {Y : Ω → Matrix n n ℂ}
    (h : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) : (expectation μ Y).IsHermitian := by
  show (expectation μ Y)ᴴ = expectation μ Y
  ext i j
  rw [Matrix.conjTranspose_apply, expectation_apply, expectation_apply]
  rw [show star (∫ ω, Y ω j i ∂μ) = ∫ ω, (starRingEnd ℂ) (Y ω j i) ∂μ from
    integral_conj.symm]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with ω hω
  calc (starRingEnd ℂ) (Y ω j i) = (Y ω)ᴴ i j := rfl
    _ = Y ω i j := by rw [hω]

end Helpers

section Defs

variable (μ)

/-- **Book eq. (2.2.3) (§2.2.6)**: the **matrix-valued variance**
`mVar(Y) = 𝔼(Y − 𝔼Y)²` of a random Hermitian matrix. Explicit source declaration. -/
noncomputable def matrixVar (Y : Ω → Matrix n n ℂ) : Matrix n n ℂ :=
  expectation μ fun ω => (Y ω - expectation μ Y) * (Y ω - expectation μ Y)

/-- **Book eq. (2.2.4) (§2.2.6)**: the **matrix variance
statistic** `v(Y) = ‖mVar(Y)‖`. Explicit source declaration. -/
noncomputable def varStatHerm (Y : Ω → Matrix n n ℂ) : ℝ :=
  ‖matrixVar μ Y‖

end Defs

section Identities

variable [MeasureTheory.IsProbabilityMeasure μ]
variable {Y : Ω → Matrix n n ℂ}

/-- Lean implementation helper: expansion of the centered square. -/
lemma centered_sq_expand (C : Matrix n n ℂ) (M : Matrix n n ℂ) :
    (M - C) * (M - C) = M * M - M * C - C * M + C * C := by
  noncomm_ring

/-- Lean implementation helper: integrability of the centered square. -/
lemma MIntegrable.centered_sq (hY : MIntegrable Y μ)
    (hY2 : MIntegrable (fun ω => Y ω * Y ω) μ) :
    MIntegrable (fun ω => (Y ω - expectation μ Y) * (Y ω - expectation μ Y)) μ := by
  have h1 : (fun ω => (Y ω - expectation μ Y) * (Y ω - expectation μ Y)) =
      fun ω => Y ω * Y ω - Y ω * expectation μ Y - expectation μ Y * Y ω +
        expectation μ Y * expectation μ Y := by
    funext ω
    exact centered_sq_expand _ _
  rw [h1]
  exact ((hY2.sub (hY.mul_const _)).sub (hY.const_mul _)).add (MIntegrable.const _)

/-- **Book eq. (2.2.3), second equality (§2.2.6)**: `mVar(Y) = 𝔼Y² − (𝔼Y)²`. Implicit
source claim (asserted inside the display). -/
theorem matrixVar_eq_sub (hY : MIntegrable Y μ)
    (hY2 : MIntegrable (fun ω => Y ω * Y ω) μ) :
    matrixVar μ Y = expectation μ (fun ω => Y ω * Y ω) -
      expectation μ Y * expectation μ Y := by
  rw [matrixVar]
  have h1 : (fun ω => (Y ω - expectation μ Y) * (Y ω - expectation μ Y)) =
      fun ω => (Y ω * Y ω - Y ω * expectation μ Y - expectation μ Y * Y ω) +
        expectation μ Y * expectation μ Y := by
    funext ω
    rw [centered_sq_expand]
  rw [h1, expectation_add ((hY2.sub (hY.mul_const _)).sub (hY.const_mul _))
      (MIntegrable.const _),
    expectation_sub (hY2.sub (hY.mul_const _)) (hY.const_mul _),
    expectation_sub hY2 (hY.mul_const _), expectation_mul_const hY,
    expectation_const_mul hY, expectation_const]
  abel

/-- **Book §2.2.6, p. 27**: "The matrix `mVar(Y)` is always positive semidefinite."
Implicit source claim. -/
theorem posSemidef_matrixVar (hY : MIntegrable Y μ)
    (hY2 : MIntegrable (fun ω => Y ω * Y ω) μ)
    (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) : (matrixVar μ Y).PosSemidef := by
  refine posSemidef_expectation (hY.centered_sq hY2) ?_
  filter_upwards [hHerm] with ω hω
  exact posSemidef_sq (hω.sub (isHermitian_expectation hHerm))

/-- **Book §2.2.6, p. 28 (display)**: the `(j,k)` entry of `mVar(Y)` is the covariance of
the `j`-th and `k`-th columns of `Y`: `(mVar Y)_{jk} = 𝔼[(y₍:ⱼ₎−𝔼y₍:ⱼ₎)*(y₍:ₖ₎−𝔼y₍:ₖ₎)]`.
Explicit (unnumbered) source statement. -/
theorem matrixVar_apply (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (j k : n) :
    matrixVar μ Y j k = ∫ ω, star (fun i => Y ω i j - expectation μ Y i j) ⬝ᵥ
      (fun i => Y ω i k - expectation μ Y i k) ∂μ := by
  rw [matrixVar, expectation_apply]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hHerm] with ω hω
  have hC : (Y ω - expectation μ Y).IsHermitian := hω.sub (isHermitian_expectation hHerm)
  show ((Y ω - expectation μ Y) * (Y ω - expectation μ Y)) j k = _
  rw [Matrix.mul_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (Y ω - expectation μ Y) j i = star ((Y ω - expectation μ Y) i j) := by
    calc (Y ω - expectation μ Y) j i = (Y ω - expectation μ Y)ᴴ j i := by rw [hC]
      _ = star ((Y ω - expectation μ Y) i j) := rfl
  rw [h1]
  rfl

/-- **Book §2.2.6, p. 28 (variational display), part 1**: `v(Y) = λ_max(mVar(Y))`.
Together with `rayleigh_matrixVar` this renders
`v(Y) = sup_{‖u‖=1} 𝔼‖Yu − 𝔼(Yu)‖²` (the sup over unit vectors of the Rayleigh value
is `λ_max` by the Prelude Rayleigh API). Implicit source declaration. -/
theorem varStatHerm_eq_lambdaMax (hY : MIntegrable Y μ)
    (hY2 : MIntegrable (fun ω => Y ω * Y ω) μ)
    (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) :
    varStatHerm μ Y = lambdaMax (posSemidef_matrixVar hY hY2 hHerm).1 :=
  posSemidef_l2_opNorm_eq_lambdaMax (posSemidef_matrixVar hY hY2 hHerm)

/-- **Book §2.2.6, p. 28 (variational display), part 2**: the Rayleigh value of `mVar(Y)`
at `u` is the variance `𝔼‖Yu − 𝔼(Yu)‖²` of the vector `Yu` in the direction `u`.
Implicit source declaration. -/
theorem rayleigh_matrixVar (hY : MIntegrable Y μ)
    (hY2 : MIntegrable (fun ω => Y ω * Y ω) μ)
    (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (u : n → ℂ) :
    rayleigh (matrixVar μ Y) u =
      ∫ ω, l2norm ((Y ω - expectation μ Y) *ᵥ u) ^ 2 ∂μ := by
  have hint := integrable_star_dotProduct (hY.centered_sq hY2) u u
  rw [show rayleigh (matrixVar μ Y) u = (star u ⬝ᵥ (matrixVar μ Y *ᵥ u)).re from rfl,
    show (matrixVar μ Y) = expectation μ
      (fun ω => (Y ω - expectation μ Y) * (Y ω - expectation μ Y)) from rfl,
    star_dotProduct_expectation (hY.centered_sq hY2) u u,
    ← RCLike.re_to_complex, ← integral_re hint]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hHerm] with ω hω
  have hC : (Y ω - expectation μ Y).IsHermitian := hω.sub (isHermitian_expectation hHerm)
  have h1 : star u ⬝ᵥ (((Y ω - expectation μ Y) * (Y ω - expectation μ Y)) *ᵥ u) =
      star ((Y ω - expectation μ Y) *ᵥ u) ⬝ᵥ ((Y ω - expectation μ Y) *ᵥ u) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec]
    congr 1
    rw [star_mulVec, hC]
  show RCLike.re (star u ⬝ᵥ _) = _
  rw [h1, dotProduct_star_self_eq, RCLike.re_to_complex]
  exact Complex.ofReal_re _

/-- **Book §2.2.6, p. 28 (variational display), combined "max" form**:
`v(Y) = max_{‖u‖=1} 𝔼‖Yu − 𝔼(Yu)‖²` — the matrix variance statistic is the greatest
value of the directional variance over unit vectors (attained). Explicit (unnumbered)
source statement ("one may wish to rewrite"). -/
theorem varStatHerm_eq_sup_variance [Nonempty n] (hY : MIntegrable Y μ)
    (hY2 : MIntegrable (fun ω => Y ω * Y ω) μ)
    (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) :
    IsGreatest {x : ℝ | ∃ u : n → ℂ, l2norm u = 1 ∧
      x = ∫ ω, l2norm ((Y ω - expectation μ Y) *ᵥ u) ^ 2 ∂μ} (varStatHerm μ Y) := by
  constructor
  · obtain ⟨u, hu, hval⟩ :=
      exists_unit_rayleigh_eq_lambdaMax (posSemidef_matrixVar hY hY2 hHerm).1
    exact ⟨u, hu, by
      rw [← rayleigh_matrixVar hY hY2 hHerm u, hval,
        varStatHerm_eq_lambdaMax hY hY2 hHerm]⟩
  · rintro x ⟨u, hu, rfl⟩
    rw [varStatHerm_eq_lambdaMax hY hY2 hHerm, ← rayleigh_matrixVar hY hY2 hHerm u]
    exact rayleigh_le_lambdaMax_of_unit _ hu

end Identities

section Sums

variable [MeasureTheory.IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lean implementation helper (the computation displayed in eq. (2.2.5)): the
expectation of a product of sums whose cross terms vanish in expectation collapses to
the diagonal. -/
lemma expectation_sum_mul_sum {p q r : Type*} [Fintype p] [Fintype q] [Fintype r]
    [DecidableEq p] [DecidableEq q] [DecidableEq r]
    {C : ι → Ω → Matrix p q ℂ} {D : ι → Ω → Matrix q r ℂ}
    (hprod : ∀ j k, MIntegrable (fun ω => C j ω * D k ω) μ)
    (hcross : ∀ j k, j ≠ k → expectation μ (fun ω => C j ω * D k ω) = 0) :
    expectation μ (fun ω => (∑ j, C j ω) * (∑ k, D k ω)) =
      ∑ k, expectation μ (fun ω => C k ω * D k ω) := by
  have h1 : (fun ω => (∑ j, C j ω) * (∑ k, D k ω)) =
      fun ω => ∑ j, ∑ k, C j ω * D k ω := by
    funext ω
    rw [Matrix.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_sum]
  rw [h1]
  rw [expectation_finsetSum _ fun j _ => MIntegrable.finsetSum _ fun k _ => hprod j k]
  have h2 : ∀ j, expectation μ (fun ω => ∑ k, C j ω * D k ω) =
      ∑ k, expectation μ (fun ω => C j ω * D k ω) := fun j =>
    expectation_finsetSum _ fun k _ => hprod j k
  simp only [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · intro j _ hjk
    exact hcross j k hjk
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **Book eq. (2.2.5)** (§2.2.7): the matrix-valued variance
is additive over a sum of independent random Hermitian matrices,
`mVar(Σₖ Xₖ) = Σₖ mVar(Xₖ)`. Explicit source statement (the source displays the
computation, including the vanishing of the cross terms, which is the content of
`expectation_sum_mul_sum` + the product rule).

Author note: the Lean identity itself does not require separate Hermitian hypotheses. -/
theorem matrixVar_sum {X : ι → Ω → Matrix n n ℂ}
    (hind : ProbabilityTheory.iIndepFun X μ) (hmeas : ∀ k, Measurable (X k))
    (hX : ∀ k, MIntegrable (X k) μ)
    (hX2 : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ) :
    matrixVar μ (fun ω => ∑ k, X k ω) = ∑ k, matrixVar μ (X k) := by
  have hEsum : expectation μ (fun ω => ∑ k, X k ω) = ∑ k, expectation μ (X k) :=
    expectation_finsetSum _ fun k _ => hX k
  -- the centered summands
  set C : ι → Ω → Matrix n n ℂ := fun k ω => X k ω - expectation μ (X k) with hC
  have hCmeas : ∀ k, Measurable (C k) := fun k =>
    (measurable_sub_const (expectation μ (X k))).comp (hmeas k)
  have hCint : ∀ k, MIntegrable (C k) μ := fun k => (hX k).sub (MIntegrable.const _)
  have hCcent : ∀ k, expectation μ (C k) = 0 := fun k => expectation_centered (hX k)
  have hCind : ∀ j k, j ≠ k → ProbabilityTheory.IndepFun (C j) (C k) μ := fun j k hjk =>
    (hind.indepFun hjk).comp (measurable_sub_const _) (measurable_sub_const _)
  have hCsq : ∀ k, MIntegrable (fun ω => C k ω * C k ω) μ := fun k =>
    (hX k).centered_sq (hX2 k)
  have hprod : ∀ j k, MIntegrable (fun ω => C j ω * C k ω) μ := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      exact hCsq j
    · exact MIntegrable.mul_of_indepFun (hCind j k hjk) (hCint j) (hCint k)
  have hcross : ∀ j k, j ≠ k → expectation μ (fun ω => C j ω * C k ω) = 0 := by
    intro j k hjk
    rw [expectation_mul_of_indepFun (hCind j k hjk) (hCmeas j) (hCmeas k)
      (hCint j) (hCint k), hCcent, hCcent, Matrix.zero_mul]
  have hcentered : (fun ω => (∑ k, X k ω) - expectation μ (fun ω' => ∑ k, X k ω')) =
      fun ω => ∑ k, C k ω := by
    funext ω
    rw [hEsum, ← Finset.sum_sub_distrib]
  rw [matrixVar]
  have h1 : (fun ω => ((∑ k, X k ω) - expectation μ (fun ω' => ∑ k, X k ω')) *
      ((∑ k, X k ω) - expectation μ (fun ω' => ∑ k, X k ω'))) =
      fun ω => (∑ j, C j ω) * (∑ k, C k ω) := by
    funext ω
    rw [show ((∑ k, X k ω) - expectation μ (fun ω' => ∑ k, X k ω')) = ∑ k, C k ω from
      congrFun hcentered ω]
  rw [h1, expectation_sum_mul_sum hprod hcross]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

/-- **Book eq. (2.2.6)** (§2.2.7): the matrix variance statistic
of an independent Hermitian sum: `v(Σ Xₖ) = ‖Σ mVar(Xₖ)‖` — "The fact that the sum
remains inside the norm is very important." Explicit source statement.

Author note: Lean derives this statistic identity without separate Hermitian hypotheses. -/
theorem varStatHerm_sum {X : ι → Ω → Matrix n n ℂ}
    (hind : ProbabilityTheory.iIndepFun X μ) (hmeas : ∀ k, Measurable (X k))
    (hX : ∀ k, MIntegrable (X k) μ)
    (hX2 : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ) :
    varStatHerm μ (fun ω => ∑ k, X k ω) = ‖∑ k, matrixVar μ (X k)‖ := by
  rw [varStatHerm, matrixVar_sum hind hmeas hX hX2]

/-- **Book §2.2.7, p. 28**: the first of "the best general inequalities":
`v(Σ Xₖ) ≤ Σₖ v(Xₖ)`. Implicit (prose) source claim. -/
theorem varStatHerm_sum_le {X : ι → Ω → Matrix n n ℂ}
    (hind : ProbabilityTheory.iIndepFun X μ) (hmeas : ∀ k, Measurable (X k))
    (hX : ∀ k, MIntegrable (X k) μ)
    (hX2 : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ) :
    varStatHerm μ (fun ω => ∑ k, X k ω) ≤ ∑ k, varStatHerm μ (X k) := by
  rw [varStatHerm_sum hind hmeas hX hX2]
  exact norm_sum_le _ _

/-- **Book §2.2.7, p. 28**: the second of "the best general inequalities":
`Σₖ v(Xₖ) ≤ d · v(Σ Xₖ)`. Implicit (prose) source claim. -/
theorem sum_varStatHerm_le_card_mul {X : ι → Ω → Matrix n n ℂ}
    (hind : ProbabilityTheory.iIndepFun X μ) (hmeas : ∀ k, Measurable (X k))
    (hX : ∀ k, MIntegrable (X k) μ)
    (hX2 : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian) :
    ∑ k, varStatHerm μ (X k) ≤
      Fintype.card n * varStatHerm μ (fun ω => ∑ k, X k ω) := by
  have hpsd : ∀ k, (matrixVar μ (X k)).PosSemidef := fun k =>
    posSemidef_matrixVar (hX k) (hX2 k) (hHerm k)
  have hpsdsum : (∑ k, matrixVar μ (X k)).PosSemidef :=
    Matrix.posSemidef_sum _ fun k _ => hpsd k
  -- Σ v(Xₖ) ≤ Σ tr(mVar Xₖ).re = tr(Σ mVar Xₖ).re ≤ d λmax(Σ) = d ‖Σ‖ = d v(ΣX)
  have h1 : ∀ k, varStatHerm μ (X k) ≤ ((matrixVar μ (X k)).trace).re := fun k => by
    rw [varStatHerm, posSemidef_l2_opNorm_eq_lambdaMax (hpsd k)]
    exact lambdaMax_le_trace_re_of_posSemidef (hpsd k)
  have h2 : (∑ k, varStatHerm μ (X k)) ≤ ((∑ k, matrixVar μ (X k)).trace).re := by
    rw [Matrix.trace_sum]
    rw [show ((∑ k, (matrixVar μ (X k)).trace).re) = ∑ k, ((matrixVar μ (X k)).trace).re
      from Complex.re_sum _ _]
    exact Finset.sum_le_sum fun k _ => h1 k
  have h3 : ((∑ k, matrixVar μ (X k)).trace).re ≤
      Fintype.card n * lambdaMax hpsdsum.1 := by
    rw [trace_re_eq_sum_eigenvalues hpsdsum.1]
    have h4 := Finset.sum_le_card_nsmul Finset.univ (fun i => hpsdsum.1.eigenvalues i)
      (lambdaMax hpsdsum.1) (fun i _ => eigenvalues_le_lambdaMax hpsdsum.1 i)
    simpa [Finset.card_univ, nsmul_eq_mul] using h4
  have h5 : lambdaMax hpsdsum.1 = varStatHerm μ (fun ω => ∑ k, X k ω) := by
    rw [varStatHerm_sum hind hmeas hX hX2]
    exact (posSemidef_l2_opNorm_eq_lambdaMax hpsdsum).symm
  calc (∑ k, varStatHerm μ (X k)) ≤ ((∑ k, matrixVar μ (X k)).trace).re := h2
    _ ≤ Fintype.card n * lambdaMax hpsdsum.1 := h3
    _ = Fintype.card n * varStatHerm μ (fun ω => ∑ k, X k ω) := by rw [h5]

/-- Lean implementation helper: the matrix-valued variance depends only on the
distribution. -/
lemma matrixVar_of_identDistrib {X X' : Ω → Matrix n n ℂ}
    (hid : ProbabilityTheory.IdentDistrib X X' μ μ) :
    matrixVar μ X = matrixVar μ X' := by
  have hE : expectation μ X = expectation μ X' := by
    ext i j
    exact (hid.comp (measurable_entry i j)).integral_eq
  rw [matrixVar, matrixVar, hE]
  ext i j
  rw [expectation_apply, expectation_apply]
  have hg : Measurable fun M : Matrix n n ℂ =>
      ((M - expectation μ X') * (M - expectation μ X')) i j := by
    have h1 : (fun M : Matrix n n ℂ =>
        ((M - expectation μ X') * (M - expectation μ X')) i j) =
        fun M : Matrix n n ℂ =>
          ∑ k, (M i k - expectation μ X' i k) * (M k j - expectation μ X' k j) := by
      funext M
      exact Matrix.mul_apply
    rw [h1]
    refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
    · exact (measurable_entry i k).sub_const _
    · exact (measurable_entry k j).sub_const _
  exact (hid.comp hg).integral_eq

/-- **Book §2.2.7, p. 28**: "when the matrices `Xₖ` are identically distributed, the
left-hand inequality becomes an identity": `v(Σ Xₖ) = Σₖ v(Xₖ)`. Implicit (prose)
source claim.

Author note: Lean formulates identical distribution relative to an arbitrary reference
index and does not add a Hermitian hypothesis. -/
theorem varStatHerm_sum_of_identDistrib [Nonempty ι] {X : ι → Ω → Matrix n n ℂ}
    (hind : ProbabilityTheory.iIndepFun X μ) (hmeas : ∀ k, Measurable (X k))
    (hX : ∀ k, MIntegrable (X k) μ)
    (hX2 : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (X k) (X (Classical.arbitrary ι)) μ μ) :
    varStatHerm μ (fun ω => ∑ k, X k ω) = ∑ k, varStatHerm μ (X k) := by
  have hsame : ∀ k, matrixVar μ (X k) = matrixVar μ (X (Classical.arbitrary ι)) :=
    fun k => matrixVar_of_identDistrib (hid k)
  rw [varStatHerm_sum hind hmeas hX hX2]
  rw [show (∑ k, matrixVar μ (X k)) =
    (Fintype.card ι) • matrixVar μ (X (Classical.arbitrary ι)) from by
      rw [Finset.sum_congr rfl fun k _ => hsame k, Finset.sum_const, Finset.card_univ]]
  rw [show (∑ k, varStatHerm μ (X k)) =
    (Fintype.card ι) • varStatHerm μ (X (Classical.arbitrary ι)) from by
      rw [Finset.sum_congr rfl fun k _ =>
        show varStatHerm μ (X k) = varStatHerm μ (X (Classical.arbitrary ι)) from by
          show ‖matrixVar μ (X k)‖ = ‖matrixVar μ (X (Classical.arbitrary ι))‖
          rw [hsame k],
        Finset.sum_const, Finset.card_univ]]
  rw [show ((Fintype.card ι) • matrixVar μ (X (Classical.arbitrary ι))) =
      ((Fintype.card ι : ℝ)) • matrixVar μ (X (Classical.arbitrary ι)) from
      (Nat.cast_smul_eq_nsmul ℝ _ _).symm]
  rw [norm_smul, nsmul_eq_mul]
  show ‖(Fintype.card ι : ℝ)‖ * ‖matrixVar μ (X (Classical.arbitrary ι))‖ = _
  rw [Real.norm_natCast]
  rfl

end Sums

end MatrixConcentration


set_option linter.unusedSectionVars false

/-!
# The variance of a rectangular random matrix (Tropp §2.2.8–§2.2.9)

* `matrixVar1`, `matrixVar2` — book eq. (2.2.7): the two
  matrix-valued variances of a general random matrix ("a general matrix has *two*
  different squares");
* `posSemidef_matrixVar1/2` — the psd claims of pp. 28–29 (implicit);
* `matrixVar1_eq_matrixVar`, `matrixVar2_eq_matrixVar` — p. 29: "the two variances
  coincide in the Hermitian setting";
* `varStat` — book eq. (2.2.8): the matrix variance
  statistic `v(Z) = max{‖mVar₁(Z)‖, ‖mVar₂(Z)‖}`, with `varStat_eq_varStatHerm`
  (consistency with (2.2.4), p. 29);
* `expectation_hermDilation`, `matrixVar_hermDilation` — book eq. (2.2.9)
: `mVar(H(Z)) = diag(mVar₁(Z), mVar₂(Z))`;
* `varStat_hermDilation` — book eq. (2.2.10):
  `v(H(Z)) = v(Z)` (using the block-diagonal norm identity of §2.2.8);
* `matrixVar1_sum`, `matrixVar2_sum` — §2.2.9 displays: additivity over an
  independent sum ("Repeating the calculation leading up to (2.2.6)");
* `varStat_sum` — book eq. (2.2.11);
* `expectation_sum_mul_conjTranspose_of_centered` — the identity (1.6.5) inside
  Theorem 1.6.2's statement: for independent centered summands,
  `𝔼(ZZ*) = Σₖ 𝔼(SₖSₖ*)` (inventory C1-06a).
-/

namespace MatrixConcentration

open Matrix MeasureTheory ProbabilityTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section Defs

variable (μ)

/-- **Book eq. (2.2.7) (§2.2.8), first variance**:
`mVar₁(Z) = 𝔼[(Z − 𝔼Z)(Z − 𝔼Z)*]` (a `d₁ × d₁` matrix describing the row
fluctuations). Explicit source declaration. -/
noncomputable def matrixVar1 (Z : Ω → Matrix m n ℂ) : Matrix m m ℂ :=
  expectation μ fun ω => (Z ω - expectation μ Z) * (Z ω - expectation μ Z)ᴴ

/-- **Book eq. (2.2.7), second variance**: `mVar₂(Z) = 𝔼[(Z − 𝔼Z)*(Z − 𝔼Z)]`.
Explicit source declaration. -/
noncomputable def matrixVar2 (Z : Ω → Matrix m n ℂ) : Matrix n n ℂ :=
  expectation μ fun ω => (Z ω - expectation μ Z)ᴴ * (Z ω - expectation μ Z)

/-- **Book eq. (2.2.8) (§2.2.8)**: the **matrix variance
statistic** of a general random matrix, `v(Z) = max{‖mVar₁(Z)‖, ‖mVar₂(Z)‖}`.
Explicit source declaration. -/
noncomputable def varStat (Z : Ω → Matrix m n ℂ) : ℝ :=
  max ‖matrixVar1 μ Z‖ ‖matrixVar2 μ Z‖

end Defs

section Basic

variable [MeasureTheory.IsProbabilityMeasure μ] {Z : Ω → Matrix m n ℂ}

/-- Lean implementation helper: integrability of the centered first square. -/
lemma MIntegrable.centered_mul_conjTranspose (hZ : MIntegrable Z μ)
    (hZ1 : MIntegrable (fun ω => Z ω * (Z ω)ᴴ) μ) :
    MIntegrable (fun ω => (Z ω - expectation μ Z) * (Z ω - expectation μ Z)ᴴ) μ := by
  have h1 : (fun ω => (Z ω - expectation μ Z) * (Z ω - expectation μ Z)ᴴ) =
      fun ω => Z ω * (Z ω)ᴴ - Z ω * (expectation μ Z)ᴴ -
        expectation μ Z * (Z ω)ᴴ + expectation μ Z * (expectation μ Z)ᴴ := by
    funext ω
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    abel
  rw [h1]
  exact ((hZ1.sub (hZ.mul_const _)).sub (hZ.conjTranspose.const_mul _)).add
    (MIntegrable.const _)

/-- Lean implementation helper: integrability of the centered second square. -/
lemma MIntegrable.conjTranspose_mul_centered (hZ : MIntegrable Z μ)
    (hZ2 : MIntegrable (fun ω => (Z ω)ᴴ * Z ω) μ) :
    MIntegrable (fun ω => (Z ω - expectation μ Z)ᴴ * (Z ω - expectation μ Z)) μ := by
  have h1 : (fun ω => (Z ω - expectation μ Z)ᴴ * (Z ω - expectation μ Z)) =
      fun ω => (Z ω)ᴴ * Z ω - (Z ω)ᴴ * expectation μ Z -
        (expectation μ Z)ᴴ * Z ω + (expectation μ Z)ᴴ * expectation μ Z := by
    funext ω
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    abel
  rw [h1]
  exact ((hZ2.sub (hZ.conjTranspose.mul_const _)).sub (hZ.const_mul _)).add
    (MIntegrable.const _)

/-- **Book §2.2.8, pp. 28–29**: "`mVar₁(Z)` is a positive-semidefinite matrix." Implicit
source claim. -/
theorem posSemidef_matrixVar1 (hZ : MIntegrable Z μ)
    (hZ1 : MIntegrable (fun ω => Z ω * (Z ω)ᴴ) μ) :
    (matrixVar1 μ Z).PosSemidef := by
  refine posSemidef_expectation (hZ.centered_mul_conjTranspose hZ1) ?_
  exact Filter.Eventually.of_forall fun ω =>
    Matrix.posSemidef_self_mul_conjTranspose _

/-- **Book §2.2.8, p. 29**: "`mVar₂(Z)` is a positive-semidefinite matrix." Implicit
source claim. -/
theorem posSemidef_matrixVar2 (hZ : MIntegrable Z μ)
    (hZ2 : MIntegrable (fun ω => (Z ω)ᴴ * Z ω) μ) :
    (matrixVar2 μ Z).PosSemidef := by
  refine posSemidef_expectation (hZ.conjTranspose_mul_centered hZ2) ?_
  exact Filter.Eventually.of_forall fun ω =>
    Matrix.posSemidef_conjTranspose_mul_self _

end Basic

section Hermitian

variable [MeasureTheory.IsProbabilityMeasure μ] {Y : Ω → Matrix n n ℂ}

/-- **Book §2.2.8, p. 29**: "For an Hermitian random matrix, `mVar(Y) = mVar₁(Y)`."
Explicit (unnumbered) source statement. -/
theorem matrixVar1_eq_matrixVar (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) :
    matrixVar1 μ Y = matrixVar μ Y := by
  rw [matrixVar1, matrixVar]
  ext i j
  rw [expectation_apply, expectation_apply]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hHerm] with ω hω
  have hC : (Y ω - expectation μ Y)ᴴ = Y ω - expectation μ Y :=
    hω.sub (isHermitian_expectation hHerm)
  rw [hC]

/-- **Book §2.2.8, p. 29**: "`mVar(Y) = mVar₂(Y)`" in the Hermitian setting. Explicit
(unnumbered) source statement. -/
theorem matrixVar2_eq_matrixVar (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) :
    matrixVar2 μ Y = matrixVar μ Y := by
  rw [matrixVar2, matrixVar]
  ext i j
  rw [expectation_apply, expectation_apply]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hHerm] with ω hω
  have hC : (Y ω - expectation μ Y)ᴴ = Y ω - expectation μ Y :=
    hω.sub (isHermitian_expectation hHerm)
  rw [hC]

/-- **Book §2.2.8, p. 29**: "When `Z` is Hermitian, the definition (2.2.8) coincides with
the original definition (2.2.4)." Explicit (unnumbered) source statement. -/
theorem varStat_eq_varStatHerm (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) :
    varStat μ Y = varStatHerm μ Y := by
  rw [varStat, matrixVar1_eq_matrixVar hHerm, matrixVar2_eq_matrixVar hHerm,
    max_self]
  rfl

end Hermitian

section DilationVariance

variable [MeasureTheory.IsProbabilityMeasure μ] {Z : Ω → Matrix m n ℂ}

/-- Lean implementation helper: expectation commutes with the Hermitian dilation. -/
lemma expectation_hermDilation (Z : Ω → Matrix m n ℂ) :
    expectation μ (fun ω => hermDilation (Z ω)) = hermDilation (expectation μ Z) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · show (∫ ω, (0 : ℂ) ∂μ) = 0
    exact MeasureTheory.integral_zero _ _
  · rfl
  · show (∫ ω, (starRingEnd ℂ) (Z ω j i) ∂μ) = (starRingEnd ℂ) (∫ ω, Z ω j i ∂μ)
    exact integral_conj
  · show (∫ ω, (0 : ℂ) ∂μ) = 0
    exact MeasureTheory.integral_zero _ _

/-- Lean implementation helper: the dilation commutes with subtraction. -/
lemma hermDilation_sub (A B : Matrix m n ℂ) :
    hermDilation (A - B) = hermDilation A - hermDilation B := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [hermDilation, Matrix.fromBlocks, Matrix.conjTranspose_sub]

/-- Lean implementation helper: expectation of a block-diagonal random matrix. -/
lemma expectation_fromBlocks_diag {A : Ω → Matrix m m ℂ} {D : Ω → Matrix n n ℂ} :
    expectation μ (fun ω => Matrix.fromBlocks (A ω) 0 0 (D ω)) =
      Matrix.fromBlocks (expectation μ A) 0 0 (expectation μ D) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · show (∫ ω, (0 : ℂ) ∂μ) = 0
    exact MeasureTheory.integral_zero _ _
  · show (∫ ω, (0 : ℂ) ∂μ) = 0
    exact MeasureTheory.integral_zero _ _
  · rfl

/-- **Book eq. (2.2.9)** (§2.2.8): the matrix-valued variance of the
Hermitian dilation is the block-diagonal matrix of the two rectangular variances:
`mVar(H(Z)) = diag(mVar₁(Z), mVar₂(Z))`. Explicit source statement (the source displays
the three-step computation, which this proof follows: definition of `mVar`, the square
identity (2.1.27), and the definitions (2.2.7)). -/
theorem matrixVar_hermDilation (Z : Ω → Matrix m n ℂ) :
    matrixVar μ (fun ω => hermDilation (Z ω)) =
      Matrix.fromBlocks (matrixVar1 μ Z) 0 0 (matrixVar2 μ Z) := by
  rw [matrixVar]
  have h1 : (fun ω => (hermDilation (Z ω) -
      expectation μ (fun ω' => hermDilation (Z ω'))) *
      (hermDilation (Z ω) - expectation μ (fun ω' => hermDilation (Z ω')))) =
      fun ω => Matrix.fromBlocks
        ((Z ω - expectation μ Z) * (Z ω - expectation μ Z)ᴴ) 0 0
        ((Z ω - expectation μ Z)ᴴ * (Z ω - expectation μ Z)) := by
    funext ω
    rw [expectation_hermDilation, ← hermDilation_sub]
    exact hermDilation_sq _
  rw [h1, expectation_fromBlocks_diag]
  rfl

/-- **Book eq. (2.2.10)** (§2.2.8): `v(H(Z)) = v(Z)` — "The
second identity holds because the spectral norm of a block-diagonal matrix is the
maximum norm achieved by one of the diagonal blocks." Explicit source statement. -/
theorem varStat_hermDilation (Z : Ω → Matrix m n ℂ) :
    varStatHerm μ (fun ω => hermDilation (Z ω)) = varStat μ Z := by
  show ‖matrixVar μ (fun ω => hermDilation (Z ω))‖ = _
  rw [matrixVar_hermDilation, l2_opNorm_fromBlocks_diagonal]
  rfl

end DilationVariance

section Sums

variable [MeasureTheory.IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Ω → Matrix m n ℂ}

/-- **Book Theorem 1.6.2, equation (1.6.4):** the identity inside its variance display
(and the §2.2.9 computation): for independent *centered* random matrices,
`𝔼(ZZ*) = Σₖ 𝔼(SₖSₖ*)` where `Z = Σₖ Sₖ`. Implicit source claim (inventory C1-06a). -/
theorem expectation_sum_mul_conjTranspose_of_centered
    (hind : ProbabilityTheory.iIndepFun S μ) (hmeas : ∀ k, Measurable (S k))
    (hS : ∀ k, MIntegrable (S k) μ)
    (hS1 : ∀ k, MIntegrable (fun ω => S k ω * (S k ω)ᴴ) μ)
    (hcent : ∀ k, expectation μ (S k) = 0) :
    expectation μ (fun ω => (∑ k, S k ω) * (∑ k, S k ω)ᴴ) =
      ∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ) := by
  have h1 : (fun ω => (∑ k, S k ω) * (∑ k, S k ω)ᴴ) =
      fun ω => (∑ j, S j ω) * (∑ k, (S k ω)ᴴ) := by
    funext ω
    rw [Matrix.conjTranspose_sum]
  rw [h1]
  refine expectation_sum_mul_sum ?_ ?_
  · intro j k
    by_cases hjk : j = k
    · subst hjk
      exact hS1 j
    · have hindk : ProbabilityTheory.IndepFun (S j) (fun ω => (S k ω)ᴴ) μ :=
        (hind.indepFun hjk).comp measurable_id measurable_conjTranspose_map
      exact MIntegrable.mul_of_indepFun hindk (hS j) (hS k).conjTranspose
  · intro j k hjk
    have hindk : ProbabilityTheory.IndepFun (S j) (fun ω => (S k ω)ᴴ) μ :=
      (hind.indepFun hjk).comp measurable_id measurable_conjTranspose_map
    rw [expectation_mul_of_indepFun hindk
      (hmeas j) (measurable_conjTranspose_map.comp (hmeas k))
      (hS j) (hS k).conjTranspose,
      hcent j, Matrix.zero_mul]

/-- **Book §2.2.9**, first displayed half: `mVar₁(Σ Sₖ) = Σₖ mVar₁(Sₖ)` for independent `Sₖ`
("Repeating the calculation leading up to (2.2.6)"). Explicit (unnumbered) source
statement. -/
theorem matrixVar1_sum
    (hind : ProbabilityTheory.iIndepFun S μ) (hmeas : ∀ k, Measurable (S k))
    (hS : ∀ k, MIntegrable (S k) μ)
    (hS1 : ∀ k, MIntegrable (fun ω => S k ω * (S k ω)ᴴ) μ) :
    matrixVar1 μ (fun ω => ∑ k, S k ω) = ∑ k, matrixVar1 μ (S k) := by
  set C : ι → Ω → Matrix m n ℂ := fun k ω => S k ω - expectation μ (S k) with hC
  have hCmeas : ∀ k, Measurable (C k) := fun k =>
    (measurable_sub_const (expectation μ (S k))).comp (hmeas k)
  have hCint : ∀ k, MIntegrable (C k) μ := fun k => (hS k).sub (MIntegrable.const _)
  have hCcent : ∀ k, expectation μ (C k) = 0 := fun k => expectation_centered (hS k)
  have hCind : ProbabilityTheory.iIndepFun C μ :=
    hind.comp _ fun k => measurable_sub_const _
  have hC1 : ∀ k, MIntegrable (fun ω => C k ω * (C k ω)ᴴ) μ := fun k =>
    (hS k).centered_mul_conjTranspose (hS1 k)
  have hEsum : expectation μ (fun ω => ∑ k, S k ω) = ∑ k, expectation μ (S k) :=
    expectation_finsetSum _ fun k _ => hS k
  have hcentered : (fun ω => (∑ k, S k ω) - expectation μ (fun ω' => ∑ k, S k ω')) =
      fun ω => ∑ k, C k ω := by
    funext ω
    rw [hEsum, ← Finset.sum_sub_distrib]
  rw [matrixVar1]
  have h2 : (fun ω => ((∑ k, S k ω) - expectation μ (fun ω' => ∑ k, S k ω')) *
      ((∑ k, S k ω) - expectation μ (fun ω' => ∑ k, S k ω'))ᴴ) =
      fun ω => (∑ k, C k ω) * (∑ k, C k ω)ᴴ := by
    funext ω
    rw [show ((∑ k, S k ω) - expectation μ (fun ω' => ∑ k, S k ω')) = ∑ k, C k ω from
      congrFun hcentered ω]
  rw [h2]
  rw [expectation_sum_mul_conjTranspose_of_centered hCind hCmeas hCint hC1 hCcent]
  rfl

/-- **Book §2.2.9**, second displayed half: `mVar₂(Σ Sₖ) = Σₖ mVar₂(Sₖ)`. Explicit (unnumbered)
source statement. -/
theorem matrixVar2_sum
    (hind : ProbabilityTheory.iIndepFun S μ) (hmeas : ∀ k, Measurable (S k))
    (hS : ∀ k, MIntegrable (S k) μ)
    (hS2 : ∀ k, MIntegrable (fun ω => (S k ω)ᴴ * S k ω) μ) :
    matrixVar2 μ (fun ω => ∑ k, S k ω) = ∑ k, matrixVar2 μ (S k) := by
  -- reduce to `matrixVar1_sum` applied to the conjugate-transposed family
  have key : ∀ (W : Ω → Matrix m n ℂ), matrixVar2 μ W =
      matrixVar1 μ (fun ω => (W ω)ᴴ) := by
    intro W
    rw [matrixVar2, matrixVar1, expectation_conjTranspose]
    ext i j
    rw [expectation_apply, expectation_apply]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ((W ω - expectation μ W)ᴴ * (W ω - expectation μ W)) i j =
      (((W ω)ᴴ - (expectation μ W)ᴴ) * ((W ω)ᴴ - (expectation μ W)ᴴ)ᴴ) i j
    rw [← Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  rw [key, show (fun ω => (∑ k, S k ω)ᴴ) = fun ω => ∑ k, (S k ω)ᴴ from
    funext fun ω => Matrix.conjTranspose_sum _ _]
  have hindT : ProbabilityTheory.iIndepFun (fun k (ω : Ω) => (S k ω)ᴴ) μ :=
    hind.comp _ fun k => measurable_conjTranspose_map
  rw [matrixVar1_sum (S := fun k (ω : Ω) => (S k ω)ᴴ) hindT
    (fun k => measurable_conjTranspose_map.comp (hmeas k))
    (fun k => (hS k).conjTranspose)
    (fun k => by
      have h2 : (fun ω => (S k ω)ᴴ * ((S k ω)ᴴ)ᴴ) = fun ω => (S k ω)ᴴ * S k ω := by
        funext ω
        rw [Matrix.conjTranspose_conjTranspose]
      rw [h2]
      exact hS2 k)]
  exact Finset.sum_congr rfl fun k _ => (key (S k)).symm

/-- **Book eq. (2.2.11)** (§2.2.9): the matrix variance statistic
of an independent sum of general random matrices:
`v(Σ Sₖ) = max{‖Σₖ mVar₁(Sₖ)‖, ‖Σₖ mVar₂(Sₖ)‖}` — "This formula arises time after
time." Explicit source statement. -/
theorem varStat_sum
    (hind : ProbabilityTheory.iIndepFun S μ) (hmeas : ∀ k, Measurable (S k))
    (hS : ∀ k, MIntegrable (S k) μ)
    (hS1 : ∀ k, MIntegrable (fun ω => S k ω * (S k ω)ᴴ) μ)
    (hS2 : ∀ k, MIntegrable (fun ω => (S k ω)ᴴ * S k ω) μ) :
    varStat μ (fun ω => ∑ k, S k ω) =
      max ‖∑ k, matrixVar1 μ (S k)‖ ‖∑ k, matrixVar2 μ (S k)‖ := by
  rw [varStat, matrixVar1_sum hind hmeas hS hS1, matrixVar2_sum hind hmeas hS hS2]

end Sums

end MatrixConcentration
