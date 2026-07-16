import MatrixConcentration.Prelude
import MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Chapter 8: Proof of Lieb's theorem

This consolidated chapter contains:

* **Book §§8.1–8.2:** matrix and vector relative entropy;
* **Book §8.3:** Klein's inequality and continuous-functional-calculus order tools;
* **Book §8.4:** integral representations and operator concavity of the logarithm;
* **Book §§8.5–8.6:** operator Jensen, matrix perspectives, and Kronecker-product identities;
* **Book §§8.7–8.8:** convexity of matrix relative entropy and Lieb's theorem;
* **Book §8.9:** monotonicity of the trace exponential.
-/

set_option linter.unusedSectionVars false

/-!
# Relative entropy: matrices and vectors (Tropp §8.1–§8.2)

Definitions and the vector-space warm-up for the proof of Lieb's theorem:

* **Definition (Matrix Relative Entropy)** (§8.1.2):
  `D(A;H) = tr[A(log A − log H) − (A − H)]` (`mre`);
* **Definition (Relative Entropy)** for positive vectors (§8.2.1): `vre`;
* the §8.2.1 prose bridge `D(a;h) = D(diag a; diag h)` —
  `vre_eq_mre_diagonal` (via the Chapter-2 `cfc_diagonal_real`);
* **Proposition 8.2.2 (Relative Entropy is Nonnegative)**  `vre_nonneg`,
  via the tangent-line inequality for the convex function `a log a − a`
  (`entropy_tangent_nonneg` — the book's displayed numerical inequality);
* **Definition (Perspective Transformation)** (§8.2.3): `perspectiveFun`;
* **Fact 8.2.4 (Perspectives are Convex)**  `perspectiveFun_convexOn`, with
  the book's proof by the secondary interpolation parameters `s = τa₁/a`;
* **Proposition 8.2.5 (Relative Entropy is Convex)**  `vre_convexOn`, by
  representing the summands as the perspective of the operator-convexity
  workhorse `f₀(a) = a − 1 − log a` (`perspective_entropy_eq`,
  `entropyKernel_convexOn`).

Convexity statements are rendered in the book's two-point display form
(`τ ∈ [0,1]`, `τ̄ = 1 − τ`).
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

section Definitions

/-- **Book §8.1.2, Definition (Matrix Relative Entropy)**  the entropy of `A`
relative to `H` is `D(A;H) = tr[A(log A − log H) − (A − H)]` (positive
definite `A`, `H`; the real part realizes the book's real-valued trace). -/
noncomputable def mre (A H : Matrix n n ℂ) : ℝ :=
  ((A * (CFC.log A - CFC.log H) - (A - H)).trace).re

/-- **Book §8.2.1, Definition (Relative Entropy)**  for positive vectors,
`D(a;h) = Σ_k [a_k(log a_k − log h_k) − (a_k − h_k)]`. -/
noncomputable def vre (a h : n → ℝ) : ℝ :=
  ∑ k, (a k * (Real.log (a k) - Real.log (h k)) - (a k - h k))

/-- **Book §8.2.1 prose**  "the vector relative entropy is a special case of
the matrix relative entropy": `D(a;h) = D(diag a; diag h)`.  Implicit source
claim (via the diagonal functional calculus). -/
lemma vre_eq_mre_diagonal {a h : n → ℝ} :
    vre a h = mre (Matrix.diagonal (RCLike.ofReal ∘ a) : Matrix n n ℂ)
      (Matrix.diagonal (RCLike.ofReal ∘ h) : Matrix n n ℂ) := by
  have hlogA : CFC.log (Matrix.diagonal (RCLike.ofReal ∘ a) : Matrix n n ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ (Real.log ∘ a)) := by
    unfold CFC.log
    have h1 := cfc_diagonal_real a Real.log
    rw [h1]
  have hlogH : CFC.log (Matrix.diagonal (RCLike.ofReal ∘ h) : Matrix n n ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ (Real.log ∘ h)) := by
    unfold CFC.log
    have h1 := cfc_diagonal_real h Real.log
    rw [h1]
  rw [mre, hlogA, hlogH, Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_sub, Matrix.diagonal_sub, Matrix.trace_diagonal]
  rw [vre, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.sub_re, Complex.mul_re]

end Definitions

section Nonnegativity

/-- **Book §8.2.2, displayed numerical inequality** (the tangent-line bound
for the convex function `f(a) = a log a − a`):
`a(log a − log h) − (a − h) ≥ 0` for positive `a` and `h`.  Explicit source
display (from `log x ≥ 1 − 1/x`). -/
lemma entropy_tangent_nonneg {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    0 ≤ a * (Real.log a - Real.log h) - (a - h) := by
  have h2 := Real.log_le_sub_one_of_pos (show 0 < h / a by positivity)
  have h3 : Real.log (h / a) = Real.log h - Real.log a :=
    Real.log_div hh.ne' ha.ne'
  rw [h3] at h2
  -- `log h − log a ≤ h/a − 1`; multiply by `a > 0` and rearrange
  have h4 := mul_le_mul_of_nonneg_left h2 ha.le
  have h5 : a * (h / a - 1) = h - a := by field_simp
  nlinarith [h4, h5]

/-- **Book Proposition 8.2.2 (Relative Entropy is Nonnegative).**
The conclusion is `D(a;h) ≥ 0` for positive vectors. Explicit source
declaration with proof (sum the tangent-line inequality). -/
theorem vre_nonneg {a h : n → ℝ} (ha : ∀ k, 0 < a k) (hh : ∀ k, 0 < h k) :
    0 ≤ vre a h :=
  Finset.sum_nonneg fun k _ => entropy_tangent_nonneg (ha k) (hh k)

end Nonnegativity

section Perspective

/-- **Book §8.2.3, Definition (Perspective Transformation)** 
`ψ_f(a;h) = a·f(h/a)` for a convex `f` on the positive real line. -/
noncomputable def perspectiveFun (f : ℝ → ℝ) (a h : ℝ) : ℝ := a * f (h / a)

/-- **Book Fact 8.2.4 (Perspectives are Convex).**
for `f` convex on the positive reals and positive `a_i`, `h_i`,
`ψ_f(τa₁+τ̄a₂; τh₁+τ̄h₂) ≤ τψ_f(a₁;h₁) + τ̄ψ_f(a₂;h₂)`.  Explicit source
declaration with proof (the secondary interpolation parameters
`s = τa₁/a`, `s̄ = τ̄a₂/a`). -/
theorem perspectiveFun_convexOn {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Set.Ioi 0) f) {a₁ a₂ h₁ h₂ τ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    perspectiveFun f (τ * a₁ + (1 - τ) * a₂) (τ * h₁ + (1 - τ) * h₂) ≤
      τ * perspectiveFun f a₁ h₁ + (1 - τ) * perspectiveFun f a₂ h₂ := by
  obtain ⟨hτ0, hτ1⟩ := hτ
  set a : ℝ := τ * a₁ + (1 - τ) * a₂ with hadef
  have hapos : 0 < a := by
    rcases eq_or_lt_of_le hτ0 with h0 | hpos
    · simp only [hadef, ← h0]
      nlinarith [ha₂]
    · rcases eq_or_lt_of_le hτ1 with h1 | hlt
      · simp only [hadef, h1]
        nlinarith [ha₁]
      · nlinarith [ha₁, ha₂]
  -- the secondary interpolation parameters
  set s : ℝ := τ * a₁ / a with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hs_sum : s + (1 - τ) * a₂ / a = 1 := by
    rw [hsdef, ← add_div, ← hadef, div_self hapos.ne']
  have hsbar : 1 - s = (1 - τ) * a₂ / a := by linarith
  have hs1 : s ≤ 1 := by
    have h1 : 0 ≤ (1 - τ) * a₂ / a := by positivity
    linarith
  -- `h/a` as an `s`-convex combination of `h₁/a₁` and `h₂/a₂`
  have hharg : (τ * h₁ + (1 - τ) * h₂) / a =
      s * (h₁ / a₁) + (1 - s) * (h₂ / a₂) := by
    rw [hsdef, hsbar]
    field_simp
  have hcvx := hf.2 (Set.mem_Ioi.mpr (show 0 < h₁ / a₁ by positivity))
    (Set.mem_Ioi.mpr (show 0 < h₂ / a₂ by positivity)) hs0
    (by linarith : (0 : ℝ) ≤ 1 - s) (by ring)
  simp only [smul_eq_mul] at hcvx
  calc perspectiveFun f a (τ * h₁ + (1 - τ) * h₂)
      = a * f (s * (h₁ / a₁) + (1 - s) * (h₂ / a₂)) := by
        rw [perspectiveFun, hharg]
    _ ≤ a * (s * f (h₁ / a₁) + (1 - s) * f (h₂ / a₂)) :=
        mul_le_mul_of_nonneg_left hcvx hapos.le
    _ = τ * perspectiveFun f a₁ h₁ + (1 - τ) * perspectiveFun f a₂ h₂ := by
        rw [perspectiveFun, perspectiveFun, hsdef, hsbar]
        field_simp

end Perspective

section Convexity

/-- Lean implementation helper: the operator-convexity workhorse
`f₀(a) = a − 1 − log a` is convex on the positive real line (affine plus
`−log`). -/
lemma entropyKernel_convexOn :
    ConvexOn ℝ (Set.Ioi 0) (fun a : ℝ => a - 1 - Real.log a) := by
  have h1 : ConvexOn ℝ (Set.Ioi 0) (fun a : ℝ => a - 1) :=
    (convexOn_id (convex_Ioi 0)).sub (concaveOn_const 1 (convex_Ioi 0))
  have h2 : ConvexOn ℝ (Set.Ioi 0) (fun a : ℝ => -Real.log a) :=
    strictConcaveOn_log_Ioi.concaveOn.neg
  have h3 := h1.add h2
  refine h3.congr fun a _ => ?_
  simp only [Pi.add_apply]
  ring

/-- **Book §8.2.4, displayed computation**  the perspective of
`f₀(a) = a − 1 − log a` is the relative-entropy summand,
`ψ_{f₀}(a;h) = a(log a − log h) − (a − h)`.  Explicit source display. -/
lemma perspective_entropy_eq {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    perspectiveFun (fun x => x - 1 - Real.log x) a h =
      a * (Real.log a - Real.log h) - (a - h) := by
  rw [perspectiveFun, Real.log_div hh.ne' ha.ne']
  field_simp
  ring

/-- **Book Proposition 8.2.5 (Relative Entropy is Convex).**
For positive vectors `a_i`, `h_i`,
`D(τa₁+τ̄a₂; τh₁+τ̄h₂) ≤ τD(a₁;h₁) + τ̄D(a₂;h₂)`.  Explicit source
declaration with proof (sum of perspectives of `f₀`). -/
theorem vre_convexOn {a₁ a₂ h₁ h₂ : n → ℝ} {τ : ℝ}
    (ha₁ : ∀ k, 0 < a₁ k) (ha₂ : ∀ k, 0 < a₂ k)
    (hh₁ : ∀ k, 0 < h₁ k) (hh₂ : ∀ k, 0 < h₂ k)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    vre (fun k => τ * a₁ k + (1 - τ) * a₂ k)
        (fun k => τ * h₁ k + (1 - τ) * h₂ k) ≤
      τ * vre a₁ h₁ + (1 - τ) * vre a₂ h₂ := by
  obtain ⟨hτ0, hτ1⟩ := hτ
  rw [vre, vre, vre, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have hapos : 0 < τ * a₁ k + (1 - τ) * a₂ k := by
    rcases eq_or_lt_of_le hτ0 with h0 | hpos
    · rw [← h0]
      nlinarith [ha₂ k]
    · rcases eq_or_lt_of_le hτ1 with h1 | hlt
      · rw [h1]
        nlinarith [ha₁ k]
      · nlinarith [ha₁ k, ha₂ k]
  have hhpos : 0 < τ * h₁ k + (1 - τ) * h₂ k := by
    rcases eq_or_lt_of_le hτ0 with h0 | hpos
    · rw [← h0]
      nlinarith [hh₂ k]
    · rcases eq_or_lt_of_le hτ1 with h1 | hlt
      · rw [h1]
        nlinarith [hh₁ k]
      · nlinarith [hh₁ k, hh₂ k]
  have h1 := perspectiveFun_convexOn entropyKernel_convexOn (ha₁ k) (ha₂ k)
    (hh₁ k) (hh₂ k) ⟨hτ0, hτ1⟩
  rw [perspective_entropy_eq hapos hhpos, perspective_entropy_eq (ha₁ k)
    (hh₁ k), perspective_entropy_eq (ha₂ k) (hh₂ k)] at h1
  exact h1

end Convexity

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The generalized Klein inequality and MRE nonnegativity (Tropp §8.3.5)

* **Proposition 8.3.5 (Generalized Klein Inequality)** 
  if `Σ_i f_i(a)g_i(h) ≥ 0` on `I × I` then
  `Σ_i tr[f_i(A)g_i(H)] ≥ 0` for Hermitian matrices with spectra in `I`
  (`generalized_klein`).  The engine is the double-eigendecomposition
  identity `tr[f(A)g(H)] = Σ_{jk} f(λ_j)g(μ_k)|⟨u_j, v_k⟩|²`
  (`trace_cfc_mul_cfc_eq_sum`), built from the outer-product spectral form
  `f(A) = Σ_j f(λ_j)·u_ju_j*` (`cfc_eq_sum_outer`) — the book's
  "eigenvalue decompositions, redux".

* the **(ungeneralized) Klein inequality** (§8.3.5 display):
  `tr f(A) ≥ tr[f(H) + f'(H)(A−H)]` whenever the scalar tangent-line bound
  holds on `I` (`klein_inequality`); the Lean proof runs the same double
  decomposition with the doubly stochastic weights `w_{jk} = |⟨u_j,v_k⟩|²`
  (marginals from Parseval, inside the proof).

* **Proposition 8.1.3 (Matrix Relative Entropy is Nonnegative)** 
  `D(A;H) ≥ 0` for positive-definite `A`, `H`
  (`mre_nonneg`) — Klein for `f(a) = a log a − a`, `f'(h) = log h`, with the
  scalar tangent bound `entropy_tangent_nonneg` from §8.2.

Supporting plumbing: `continuousOn_matrix_spectrum` (every real function is
continuous on the finite spectrum of a matrix, so the `cfc` calculus is
total here), `spectrum_subset_Ioi`, and the `cfc`-algebra conversion
`cfc_entropy_eq`.
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A H : Matrix n n ℂ}

section OuterProducts

/-- Lean implementation helper: a unitary conjugation of a real diagonal
matrix as a sum of weighted outer products of the basis columns (the book's
"eigenvalue decompositions, redux": `A = Σ_i λ_i u_iu_i*`). -/
lemma conj_diagonal_eq_sum_outer (hA : A.IsHermitian) (v : n → ℝ) :
    (hA.eigenvectorUnitary : Matrix n n ℂ) *
        (Matrix.diagonal (RCLike.ofReal ∘ v) : Matrix n n ℂ) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ =
      ∑ j, ((v j : ℝ) : ℂ) • Matrix.vecMulVec (⇑(hA.eigenvectorBasis j))
        (star ⇑(hA.eigenvectorBasis j)) := by
  ext a b
  rw [Matrix.mul_apply, Matrix.sum_apply]
  have h1 : ∀ c, ((hA.eigenvectorUnitary : Matrix n n ℂ) *
      (Matrix.diagonal (RCLike.ofReal ∘ v) : Matrix n n ℂ)) a c =
      (hA.eigenvectorUnitary : Matrix n n ℂ) a c * ((v c : ℝ) : ℂ) := by
    intro c
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single c (fun e _ he => by
      rw [Matrix.diagonal_apply_ne _ he, mul_zero])
      (fun h => absurd (Finset.mem_univ c) h)]
    rw [Matrix.diagonal_apply_eq]
    rfl
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h1 c, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Matrix.conjTranspose_apply]
  have h2 : (hA.eigenvectorUnitary : Matrix n n ℂ) a c =
      ⇑(hA.eigenvectorBasis c) a := hA.eigenvectorUnitary_apply a c
  have h3 : (hA.eigenvectorUnitary : Matrix n n ℂ) b c =
      ⇑(hA.eigenvectorBasis c) b := hA.eigenvectorUnitary_apply b c
  rw [h2, h3]
  simp only [Pi.star_apply, RCLike.star_def, smul_eq_mul]
  ring

/-- Lean implementation helper: the outer-product spectral form of a
standard matrix function, `f(A) = Σ_j f(λ_j)·u_ju_j*`. -/
lemma cfc_eq_sum_outer (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = ∑ j, ((f (hA.eigenvalues j) : ℝ) : ℂ) •
      Matrix.vecMulVec (⇑(hA.eigenvectorBasis j))
        (star ⇑(hA.eigenvectorBasis j)) := by
  rw [cfc_eq_book_formula hA f]
  exact conj_diagonal_eq_sum_outer hA (f ∘ hA.eigenvalues)

/-- Lean implementation helper: the trace of a product of two rank-one
outer products is the squared inner product (the book's "we identify the
trace as a squared inner product"). -/
lemma trace_outer_mul_outer (u v : n → ℂ) :
    (Matrix.vecMulVec u (star u) * Matrix.vecMulVec v (star v)).trace =
      ((‖star u ⬝ᵥ v‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ∀ a, (Matrix.vecMulVec u (star u) *
      Matrix.vecMulVec v (star v)) a a =
      u a * (star u ⬝ᵥ v) * star (v a) := by
    intro a
    rw [Matrix.mul_apply]
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, dotProduct,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have h4 : (Matrix.vecMulVec u (star u) *
      Matrix.vecMulVec v (star v)).trace =
      ∑ a, u a * (star u ⬝ᵥ v) * star (v a) := by
    rw [Matrix.trace]
    exact Finset.sum_congr rfl fun a _ => h1 a
  rw [h4]
  have h2 : ∑ a, u a * (star u ⬝ᵥ v) * star (v a) =
      (star u ⬝ᵥ v) * ∑ a, star (v a) * u a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => by ring
  rw [h2]
  have h3 : (∑ a, star (v a) * u a) = star (star u ⬝ᵥ v) := by
    rw [dotProduct, star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.star_apply, star_mul', star_star]
    ring
  rw [h3, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Book Proposition 8.3.5, proof computation.** The double-eigendecomposition
trace identity
`tr[f(A)g(H)] = Σ_{jk} f(λ_j)g(μ_k)·|⟨u_j, v_k⟩|²`.  Recovered prerequisite
(the displayed computation of the source proof). -/
lemma trace_cfc_mul_cfc_eq_sum (hA : A.IsHermitian) (hH : H.IsHermitian)
    (f g : ℝ → ℝ) :
    ((cfc f A * cfc g H).trace).re =
      ∑ j, ∑ k, f (hA.eigenvalues j) * g (hH.eigenvalues k) *
        ‖star (⇑(hA.eigenvectorBasis j)) ⬝ᵥ ⇑(hH.eigenvectorBasis k)‖ ^ 2
      := by
  rw [cfc_eq_sum_outer hA f, cfc_eq_sum_outer hH g, Finset.sum_mul]
  have h1 : ∀ j, (((f (hA.eigenvalues j) : ℝ) : ℂ) •
      Matrix.vecMulVec (⇑(hA.eigenvectorBasis j))
        (star ⇑(hA.eigenvectorBasis j))) *
      (∑ k, ((g (hH.eigenvalues k) : ℝ) : ℂ) •
        Matrix.vecMulVec (⇑(hH.eigenvectorBasis k))
          (star ⇑(hH.eigenvectorBasis k))) =
      ∑ k, (((f (hA.eigenvalues j) * g (hH.eigenvalues k) : ℝ) : ℂ)) •
        (Matrix.vecMulVec (⇑(hA.eigenvectorBasis j))
          (star ⇑(hA.eigenvectorBasis j)) *
        Matrix.vecMulVec (⇑(hH.eigenvectorBasis k))
          (star ⇑(hH.eigenvectorBasis k))) := by
    intro j
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ => h1 j, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.trace_smul, trace_outer_mul_outer, smul_eq_mul,
    ← Complex.ofReal_mul, Complex.ofReal_re]

end OuterProducts

section Weights

/-- Lean implementation helper: the inner product of `EuclideanSpace`
matches the project's `star · ⬝ᵥ ·` convention. -/
lemma inner_eq_star_dotProduct (x y : EuclideanSpace ℂ n) :
    (inner ℂ x y : ℂ) = star (⇑x : n → ℂ) ⬝ᵥ (⇑y : n → ℂ) := by
  rw [PiLp.inner_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply]
  simp only [Pi.star_apply, RCLike.star_def]
  ring

/-- Lean implementation helper: conjugate symmetry of the overlap norm. -/
lemma norm_star_dotProduct_comm (u v : n → ℂ) :
    ‖star u ⬝ᵥ v‖ = ‖star v ⬝ᵥ u‖ := by
  have h1 : star v ⬝ᵥ u = star (star u ⬝ᵥ v) := by
    rw [dotProduct, dotProduct, star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.star_apply, star_mul', star_star]
    ring
  rw [h1, norm_star]

/-- Lean implementation helper (Parseval): for an orthonormal basis
`{v_k}`, the overlaps of any `u` satisfy `Σ_k |⟨u, v_k⟩|² = ‖u‖²`. -/
lemma sum_sq_overlap (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n))
    (u : EuclideanSpace ℂ n) :
    ∑ k, ‖star (⇑u : n → ℂ) ⬝ᵥ (⇑(b k) : n → ℂ)‖ ^ 2 = ‖u‖ ^ 2 := by
  have h1 : ∀ k, ‖star (⇑u : n → ℂ) ⬝ᵥ (⇑(b k) : n → ℂ)‖ ^ 2 =
      ‖b.repr u k‖ ^ 2 := by
    intro k
    rw [b.repr_apply_apply, inner_eq_star_dotProduct,
      norm_star_dotProduct_comm]
  rw [Finset.sum_congr rfl fun k _ => h1 k]
  have h2 : ‖b.repr u‖ ^ 2 = ∑ k, ‖b.repr u k‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun k _ => by positivity)]
  rw [← h2, b.repr.norm_map]

end Weights

section Klein

/-- Lean implementation helper: every real function is continuous on the
(finite, hence discrete) real spectrum of a matrix — the `cfc` calculus on
matrices is total. -/
lemma continuousOn_matrix_spectrum (f : ℝ → ℝ) (A : Matrix n n ℂ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [continuousOn_iff_continuous_restrict]
  haveI : DiscreteTopology (spectrum ℝ A) := by
    have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
    haveI : Finite (spectrum ℝ A) := hfin
    infer_instance
  exact continuous_of_discreteTopology

/-- Lean implementation helper: the real spectrum of a positive-definite
matrix lies in the open positive axis. -/
lemma spectrum_subset_Ioi (hA : A.PosDef) :
    spectrum ℝ A ⊆ Set.Ioi (0 : ℝ) := by
  rw [hA.1.spectrum_real_eq_range_eigenvalues]
  rintro x ⟨i, rfl⟩
  exact hA.eigenvalues_pos i

/-- **Book Proposition 8.3.5 (Generalized Klein Inequality).**
If `Σ_i f_i(a)g_i(h) ≥ 0` for all `a, h ∈ I`, then
`Σ_i tr[f_i(A)g_i(H)] ≥ 0` for Hermitian `A`, `H` with eigenvalues in `I`.
Explicit source declaration with proof (double eigendecomposition). -/
theorem generalized_klein {ι : Type*} [Fintype ι] (f g : ι → ℝ → ℝ)
    {I : Set ℝ} (hfg : ∀ a ∈ I, ∀ h ∈ I, 0 ≤ ∑ i, f i a * g i h)
    (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hAI : ∀ j, hA.eigenvalues j ∈ I) (hHI : ∀ k, hH.eigenvalues k ∈ I) :
    0 ≤ ∑ i, ((cfc (f i) A * cfc (g i) H).trace).re := by
  have h1 : ∀ i : ι, ((cfc (f i) A * cfc (g i) H).trace).re =
      ∑ j, ∑ k, f i (hA.eigenvalues j) * g i (hH.eigenvalues k) *
        ‖star (⇑(hA.eigenvectorBasis j)) ⬝ᵥ ⇑(hH.eigenvectorBasis k)‖ ^ 2 :=
    fun i => trace_cfc_mul_cfc_eq_sum hA hH (f i) (g i)
  rw [Finset.sum_congr rfl fun i _ => h1 i]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun k _ => ?_
  have h2 : ∑ i, f i (hA.eigenvalues j) * g i (hH.eigenvalues k) *
      ‖star (⇑(hA.eigenvectorBasis j)) ⬝ᵥ ⇑(hH.eigenvectorBasis k)‖ ^ 2 =
      (∑ i, f i (hA.eigenvalues j) * g i (hH.eigenvalues k)) *
      ‖star (⇑(hA.eigenvectorBasis j)) ⬝ᵥ ⇑(hH.eigenvectorBasis k)‖ ^ 2 :=
    (Finset.sum_mul _ _ _).symm
  rw [h2]
  exact mul_nonneg (hfg _ (hAI j) _ (hHI k)) (by positivity)

/-- **Book §8.3.5, first display** (the (ungeneralized) **Klein
inequality**): if the tangent-line bound `f(a) − f(h) − f'(h)(a − h) ≥ 0`
holds on `I × I`, then `tr[f(H) + f'(H)(A − H)] ≤ tr f(A)` for Hermitian
matrices with spectra in `I`.  Explicit source display; the Lean proof runs
the double eigendecomposition with the doubly stochastic weights
`w_{jk} = |⟨u_j, v_k⟩|²`.

Author note: finite-dimensional functional calculus lets Lean state the inequality without separate continuity hypotheses on the scalar functions. -/
theorem klein_inequality {f f' : ℝ → ℝ} {I : Set ℝ}
    (htangent : ∀ a ∈ I, ∀ h ∈ I, 0 ≤ f a - f h - f' h * (a - h))
    (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hAI : ∀ j, hA.eigenvalues j ∈ I) (hHI : ∀ k, hH.eigenvalues k ∈ I) :
    ((cfc f H).trace).re + ((cfc f' H * (A - H)).trace).re ≤
      ((cfc f A).trace).re := by
  classical
  have hsaA : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  have hsaH : IsSelfAdjoint H := Matrix.isHermitian_iff_isSelfAdjoint.mp hH
  set w : n → n → ℝ := fun j k =>
    ‖star (⇑(hA.eigenvectorBasis j)) ⬝ᵥ ⇑(hH.eigenvectorBasis k)‖ ^ 2
    with hwdef
  have hw0 : ∀ j k, 0 ≤ w j k := fun j k => by positivity
  have hnormA : ∀ j, ‖hA.eigenvectorBasis j‖ = 1 := fun j =>
    hA.eigenvectorBasis.orthonormal.1 j
  have hnormH : ∀ k, ‖hH.eigenvectorBasis k‖ = 1 := fun k =>
    hH.eigenvectorBasis.orthonormal.1 k
  have hright : ∀ j, ∑ k, w j k = 1 := by
    intro j
    have h1 := sum_sq_overlap hH.eigenvectorBasis (hA.eigenvectorBasis j)
    rw [hnormA j] at h1
    simpa using h1
  have hleft : ∀ k, ∑ j, w j k = 1 := by
    intro k
    have h1 := sum_sq_overlap hA.eigenvectorBasis (hH.eigenvectorBasis k)
    rw [hnormH k] at h1
    have h2 : ∀ j, w j k = ‖star (⇑(hH.eigenvectorBasis k)) ⬝ᵥ
        ⇑(hA.eigenvectorBasis j)‖ ^ 2 := fun j => by
      rw [hwdef]
      simp only
      rw [norm_star_dotProduct_comm]
    rw [Finset.sum_congr rfl fun j _ => h2 j]
    simpa using h1
  -- the four traces as weighted double sums
  have hfA : ((cfc f A).trace).re = ∑ j, ∑ k, f (hA.eigenvalues j) * w j k
      := by
    have h1 := trace_cfc_eq_sum hA f
    rw [h1, Complex.ofReal_re]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, hright j, mul_one]
  have hfH : ((cfc f H).trace).re = ∑ j, ∑ k, f (hH.eigenvalues k) * w j k
      := by
    have h1 := trace_cfc_eq_sum hH f
    rw [h1, Complex.ofReal_re, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_sum, hleft k, mul_one]
  have hfA' : ((cfc f' H * A).trace).re =
      ∑ j, ∑ k, f' (hH.eigenvalues k) * hA.eigenvalues j * w j k := by
    have h1 : cfc (id : ℝ → ℝ) A = A := cfc_id ℝ A
    have h2 := trace_cfc_mul_cfc_eq_sum hA hH (id : ℝ → ℝ) f'
    rw [h1] at h2
    rw [Matrix.trace_mul_comm, h2]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [id_eq]
    ring
  have hfH' : ((cfc f' H * H).trace).re =
      ∑ j, ∑ k, f' (hH.eigenvalues k) * hH.eigenvalues k * w j k := by
    have h1 : cfc f' H * H = cfc (fun h : ℝ => f' h * h) H := by
      have h2 := cfc_mul f' (id : ℝ → ℝ) H
        (continuousOn_matrix_spectrum _ H) (continuousOn_matrix_spectrum _ H)
      rw [show (fun h : ℝ => f' h * h) = fun x : ℝ => f' x * id x from rfl,
        h2, cfc_id ℝ H]
    rw [h1]
    have h3 := trace_cfc_eq_sum hH (fun h : ℝ => f' h * h)
    rw [h3, Complex.ofReal_re, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_sum, hleft k, mul_one]
  have hexpand : ((cfc f' H * (A - H)).trace).re =
      ((cfc f' H * A).trace).re - ((cfc f' H * H).trace).re := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [hexpand, hfA, hfH, hfA', hfH']
  have hkey : ∀ j k, f (hH.eigenvalues k) * w j k +
      (f' (hH.eigenvalues k) * hA.eigenvalues j * w j k -
        f' (hH.eigenvalues k) * hH.eigenvalues k * w j k) ≤
      f (hA.eigenvalues j) * w j k := by
    intro j k
    have h1 := htangent (hA.eigenvalues j) (hAI j) (hH.eigenvalues k) (hHI k)
    nlinarith [mul_nonneg h1 (hw0 j k)]
  calc (∑ j, ∑ k, f (hH.eigenvalues k) * w j k) +
      ((∑ j, ∑ k, f' (hH.eigenvalues k) * hA.eigenvalues j * w j k) -
        ∑ j, ∑ k, f' (hH.eigenvalues k) * hH.eigenvalues k * w j k)
      = ∑ j, ∑ k, (f (hH.eigenvalues k) * w j k +
          (f' (hH.eigenvalues k) * hA.eigenvalues j * w j k -
            f' (hH.eigenvalues k) * hH.eigenvalues k * w j k)) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    _ ≤ ∑ j, ∑ k, f (hA.eigenvalues j) * w j k :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hkey j k

end Klein

section MRENonneg

/-- Lean implementation helper: `cfc (a·log a − a) = A·log A − A` (the
functional-calculus form of the §8.3.5 instantiation). -/
lemma cfc_entropy_eq (hA : A.IsHermitian) :
    cfc (fun a : ℝ => a * Real.log a - a) A = A * CFC.log A - A := by
  have hsa : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  have h1 := cfc_sub (fun a : ℝ => a * Real.log a) (fun a : ℝ => a) A
    (continuousOn_matrix_spectrum _ A) (continuousOn_matrix_spectrum _ A)
  have h2 := cfc_mul (id : ℝ → ℝ) Real.log A
    (continuousOn_matrix_spectrum _ A) (continuousOn_matrix_spectrum _ A)
  rw [show (fun a : ℝ => a * Real.log a - a) =
    fun a : ℝ => (fun x : ℝ => x * Real.log x) a - (fun x : ℝ => x) a
    from rfl, h1,
    show (fun x : ℝ => x * Real.log x) =
      fun x : ℝ => id x * Real.log x from rfl, h2, cfc_id ℝ A,
    cfc_id' ℝ A]
  rfl

/-- **Book Proposition 8.1.3 (Matrix Relative Entropy is Nonnegative).**
The conclusion is `D(A;H) ≥ 0` for positive-definite matrices.
Explicit source declaration; §8.3.5 proof (Klein inequality for
`f(a) = a log a − a`, `f'(h) = log h`). -/
theorem mre_nonneg (hA : A.PosDef) (hH : H.PosDef) : 0 ≤ mre A H := by
  have htan : ∀ a ∈ Set.Ioi (0 : ℝ), ∀ h ∈ Set.Ioi (0 : ℝ),
      0 ≤ (a * Real.log a - a) - (h * Real.log h - h) -
        Real.log h * (a - h) := by
    intro a ha h hh
    have h1 := entropy_tangent_nonneg (Set.mem_Ioi.mp ha) (Set.mem_Ioi.mp hh)
    nlinarith [h1]
  have hspecA : ∀ j, hA.1.eigenvalues j ∈ Set.Ioi (0 : ℝ) := fun j =>
    Set.mem_Ioi.mpr (hA.eigenvalues_pos j)
  have hspecH : ∀ k, hH.1.eigenvalues k ∈ Set.Ioi (0 : ℝ) := fun k =>
    Set.mem_Ioi.mpr (hH.eigenvalues_pos k)
  have h := klein_inequality (f := fun a => a * Real.log a - a)
    (f' := Real.log) htan hA.1 hH.1 hspecA hspecH
  rw [cfc_entropy_eq hA.1, cfc_entropy_eq hH.1] at h
  have hlog : cfc Real.log H = CFC.log H := rfl
  rw [hlog] at h
  have e1 : ((A * CFC.log A - A).trace).re =
      ((A * CFC.log A).trace).re - (A.trace).re := by
    rw [Matrix.trace_sub, Complex.sub_re]
  have e2 : ((H * CFC.log H - H).trace).re =
      ((H * CFC.log H).trace).re - (H.trace).re := by
    rw [Matrix.trace_sub, Complex.sub_re]
  have e3 : ((CFC.log H * (A - H)).trace).re =
      ((CFC.log H * A).trace).re - ((CFC.log H * H).trace).re := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [e1, e2, e3] at h
  have e4 : ((CFC.log H * H).trace).re = ((H * CFC.log H).trace).re := by
    rw [Matrix.trace_mul_comm]
  have e6 : ((CFC.log H * A).trace).re = ((A * CFC.log H).trace).re := by
    rw [Matrix.trace_mul_comm]
  rw [e4, e6] at h
  have e5 : mre A H = ((A * CFC.log A).trace).re -
      ((A * CFC.log H).trace).re - (A.trace).re + (H.trace).re := by
    rw [mre]
    have h6 : A * (CFC.log A - CFC.log H) - (A - H) =
        A * CFC.log A - A * CFC.log H - A + H := by
      rw [Matrix.mul_sub]
      abel
    rw [h6, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
      Complex.add_re, Complex.sub_re, Complex.sub_re]
  rw [e5]
  linarith

end MRENonneg

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# Functional-calculus/Loewner toolkit for Chapter 8

Recovered prerequisites (classification 3/4) used throughout §8.4–§8.8:

* eigenvalue-level `cfc` plumbing: `cfc_congr_of_eigenvalues`,
  `posSemidef_cfc_of_nonneg`, `posDef_cfc_of_pos`,
  `eigenvalues_le_one_of_loewner_le_one`;
* shifted resolvents: `posDef_add_smul_one`, `add_smul_one_eq_cfc`,
  `inv_shift_eq_cfc`, `inv_eq_cfc` — the identification
  `(A + uI)⁻¹ = f(A)` behind the §8.4 integral representation;
* the positive-definite square root `posSqrt A = cfc √ A` with its algebra
  (`posSqrt_posDef`, `posSqrt_mul_self`, `posSqrt_inv_eq_cfc`,
  `isHermitian_posSqrt`) — the book's `A^{1/2}`, `A^{-1/2}`;
* the §8.4.3 step "when a positive-definite matrix has eigenvalues bounded
  above by one, its inverse has eigenvalues bounded below by one":
  `one_le_inv_of_le_one`;
* the real-scalar Loewner monotonicity `smul_loewner_mono` (reproved here
  to keep Chapter 8 independent of Chapters 3–7, as required for the
  the proof of Lieb’s theorem).
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A H M : Matrix n n ℂ}

section CfcPlumbing

/-- Lean implementation helper: `cfc` respects agreement on the
eigenvalues. -/
lemma cfc_congr_of_eigenvalues (hA : A.IsHermitian) {f g : ℝ → ℝ}
    (hfg : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    cfc f A = cfc g A := by
  rw [cfc_eq_book_formula hA f, cfc_eq_book_formula hA g]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, Function.comp_apply, hfg i]
  · simp only [Matrix.diagonal_apply_ne _ hij]

/-- Lean implementation helper: `cfc g A` is psd when `g` is nonnegative on
the eigenvalues. -/
lemma posSemidef_cfc_of_nonneg (hA : A.IsHermitian) {g : ℝ → ℝ}
    (hg : ∀ i, 0 ≤ g (hA.eigenvalues i)) : (cfc g A).PosSemidef := by
  rw [cfc_eq_book_formula hA g]
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ _
  exact (posSemidef_diagonal_real_iff _).mpr fun i => hg i

/-- Lean implementation helper: `cfc g A` is pd when `g` is positive on the
eigenvalues. -/
lemma posDef_cfc_of_pos (hA : A.IsHermitian) {g : ℝ → ℝ}
    (hg : ∀ i, 0 < g (hA.eigenvalues i)) : (cfc g A).PosDef := by
  rw [posDef_iff_exists_eigenvalues_pos]
  refine ⟨isHermitian_cfc g A, fun i => ?_⟩
  have h1 : (isHermitian_cfc g A).eigenvalues i ∈
      Multiset.map ((isHermitian_cfc g A).eigenvalues) Finset.univ.val :=
    Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩
  rw [eigenvalues_cfc_multiset hA g] at h1
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp h1
  rw [← hj]
  exact hg j

/-- Lean implementation helper: real-scalar Loewner monotonicity. -/
lemma smul_loewner_mono {c : ℝ} (hc : 0 ≤ c) (hAH : A ≤ H) :
    c • A ≤ c • H := by
  rw [Matrix.le_iff, ← smul_sub]
  exact posSemidef_smul_nonneg (Matrix.le_iff.mp hAH) hc

/-- Lean implementation helper: eigenvalue bound from a Loewner bound by
the identity (Rayleigh quotient at the eigenbasis). -/
lemma eigenvalues_le_one_of_loewner_le_one (hM : M.IsHermitian)
    (hle : M ≤ 1) : ∀ i, hM.eigenvalues i ≤ 1 := by
  intro i
  have h1 : hM.eigenvalues i = rayleigh M (⇑(hM.eigenvectorBasis i)) :=
    (rayleigh_eigenvectorBasis hM i).symm
  have h2 := rayleigh_mono_of_loewner_le hle (⇑(hM.eigenvectorBasis i))
  have h3 : rayleigh 1 (⇑(hM.eigenvectorBasis i)) = 1 := by
    rw [rayleigh, Matrix.one_mulVec, dotProduct_star_self_eq,
      Complex.ofReal_re, l2norm_eigenvectorBasis hM i, one_pow]
  rw [h1]
  rw [h3] at h2
  linarith

end CfcPlumbing

section ShiftedResolvents

/-- Lean implementation helper: `A + uI` is pd for pd `A` and `u ≥ 0`. -/
lemma posDef_add_smul_one (hA : A.PosDef) {u : ℝ} (hu : 0 ≤ u) :
    (A + u • (1 : Matrix n n ℂ)).PosDef :=
  hA.add_posSemidef (posSemidef_smul_nonneg Matrix.PosSemidef.one hu)

/-- Lean implementation helper: `A + uI` as a standard matrix function. -/
lemma add_smul_one_eq_cfc (hA : A.IsHermitian) (u : ℝ) :
    A + u • (1 : Matrix n n ℂ) = cfc (fun a : ℝ => a + u) A := by
  have hsa : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  have h1 := cfc_add (a := A) (id : ℝ → ℝ) (fun _ : ℝ => u)
    (continuousOn_matrix_spectrum _ A) (continuousOn_matrix_spectrum _ A)
  rw [show (fun a : ℝ => a + u) = fun a : ℝ => id a + (fun _ : ℝ => u) a
    from rfl, h1, cfc_id ℝ A, cfc_const u A,
    Algebra.algebraMap_eq_smul_one]

/-- Lean implementation helper: the shifted resolvent as a standard matrix
function — `(A + uI)⁻¹ = f(A)` with `f(a) = (a + u)⁻¹` (`u ≥ 0`, `A` pd). -/
lemma inv_shift_eq_cfc (hA : A.PosDef) {u : ℝ} (hu : 0 ≤ u) :
    (A + u • (1 : Matrix n n ℂ))⁻¹ = cfc (fun a : ℝ => (a + u)⁻¹) A := by
  have hsa : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA.1
  refine Matrix.inv_eq_left_inv ?_
  rw [add_smul_one_eq_cfc hA.1 u]
  have h1 := cfc_mul (fun a : ℝ => (a + u)⁻¹) (fun a : ℝ => a + u) A
    (continuousOn_matrix_spectrum _ A) (continuousOn_matrix_spectrum _ A)
  rw [← h1]
  have h2 : cfc (fun a : ℝ => (a + u)⁻¹ * (a + u)) A =
      cfc (fun _ : ℝ => (1 : ℝ)) A := by
    refine cfc_congr_of_eigenvalues hA.1 fun i => ?_
    have h3 : 0 < hA.1.eigenvalues i + u :=
      add_pos_of_pos_of_nonneg (hA.eigenvalues_pos i) hu
    field_simp
  rw [h2]
  exact cfc_const_one ℝ A

/-- Lean implementation helper: the inverse of a pd matrix as a standard
matrix function. -/
lemma inv_eq_cfc (hA : A.PosDef) :
    A⁻¹ = cfc (fun a : ℝ => a⁻¹) A := by
  have h1 := inv_shift_eq_cfc hA (le_refl (0 : ℝ))
  simp only [zero_smul, add_zero] at h1
  exact h1

/-- **Book §8.4.3, middle step**  "When a positive-definite matrix has
eigenvalues bounded above by one, its inverse has eigenvalues bounded below
by one": `M pd`, `M ≼ I` implies `I ≼ M⁻¹`.  Implicit source claim. -/
lemma one_le_inv_of_le_one (hM : M.PosDef) (hle : M ≤ 1) :
    (1 : Matrix n n ℂ) ≤ M⁻¹ := by
  rw [inv_eq_cfc hM]
  have h1 : (1 : Matrix n n ℂ) = cfc (fun _ : ℝ => (1 : ℝ)) M :=
    (cfc_const_one ℝ M).symm
  rw [h1]
  refine transfer_rule hM.1 (I := {x : ℝ | 0 < x ∧ x ≤ 1})
    (fun i => ⟨hM.eigenvalues_pos i,
      eigenvalues_le_one_of_loewner_le_one hM.1 hle i⟩) fun a ha => ?_
  obtain ⟨ha0, ha1⟩ := ha
  rw [le_inv_comm₀ one_pos ha0]
  simpa using ha1

end ShiftedResolvents

section PosSqrt

/-- Lean implementation helper.

The positive square root of a psd matrix, as a standard matrix function
(the book's `A^{1/2}`). -/
noncomputable def posSqrt (M : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc Real.sqrt M

/-- Lean implementation helper: `posSqrt` is Hermitian. -/
lemma isHermitian_posSqrt (M : Matrix n n ℂ) : (posSqrt M).IsHermitian :=
  isHermitian_cfc Real.sqrt M

/-- Lean implementation helper: `posSqrt` of a pd matrix is pd (the book's
"the unique positive-definite square root"). -/
lemma posSqrt_posDef (hA : A.PosDef) : (posSqrt A).PosDef :=
  posDef_cfc_of_pos hA.1 fun i => Real.sqrt_pos.mpr (hA.eigenvalues_pos i)

/-- Lean implementation helper: `√A·√A = A` for psd `A`. -/
lemma posSqrt_mul_self (hA : A.PosSemidef) : posSqrt A * posSqrt A = A := by
  rw [posSqrt]
  have h1 := cfc_mul Real.sqrt Real.sqrt A
    (continuousOn_matrix_spectrum _ A) (continuousOn_matrix_spectrum _ A)
  rw [← h1]
  have h2 : cfc (fun a : ℝ => Real.sqrt a * Real.sqrt a) A =
      cfc (id : ℝ → ℝ) A := by
    refine cfc_congr_of_eigenvalues hA.1 fun i => ?_
    rw [Real.mul_self_sqrt (hA.eigenvalues_nonneg i)]
    rfl
  rw [h2, cfc_id ℝ A]

/-- Lean implementation helper: the inverse of `posSqrt` as a standard
matrix function (the book's `A^{-1/2}`). -/
lemma posSqrt_inv_eq_cfc (hA : A.PosDef) :
    (posSqrt A)⁻¹ = cfc (fun a : ℝ => (Real.sqrt a)⁻¹) A := by
  refine Matrix.inv_eq_left_inv ?_
  rw [posSqrt]
  have h1 := cfc_mul (fun a : ℝ => (Real.sqrt a)⁻¹) Real.sqrt A
    (continuousOn_matrix_spectrum _ A) (continuousOn_matrix_spectrum _ A)
  rw [← h1]
  have h2 : cfc (fun a : ℝ => (Real.sqrt a)⁻¹ * Real.sqrt a) A =
      cfc (fun _ : ℝ => (1 : ℝ)) A := by
    refine cfc_congr_of_eigenvalues hA.1 fun i => ?_
    have h3 : Real.sqrt (hA.1.eigenvalues i) ≠ 0 :=
      (Real.sqrt_pos.mpr (hA.eigenvalues_pos i)).ne'
    field_simp
  rw [h2]
  exact cfc_const_one ℝ A

/-- Lean implementation helper: `(√A)⁻¹` is Hermitian for pd `A`. -/
lemma isHermitian_posSqrt_inv (hA : A.PosDef) :
    ((posSqrt A)⁻¹).IsHermitian := by
  rw [posSqrt_inv_eq_cfc hA]
  exact isHermitian_cfc _ A

/-- Lean implementation helper: `(√A)⁻¹` is pd for pd `A`. -/
lemma posDef_posSqrt_inv (hA : A.PosDef) : ((posSqrt A)⁻¹).PosDef :=
  (posSqrt_posDef hA).inv

/-- Lean implementation helper: `(√A)⁻¹·√A = 1` for pd `A`. -/
lemma posSqrt_inv_mul (hA : A.PosDef) :
    (posSqrt A)⁻¹ * posSqrt A = 1 := by
  rw [posSqrt_inv_eq_cfc hA, posSqrt]
  have h1 := cfc_mul (fun a : ℝ => (Real.sqrt a)⁻¹) Real.sqrt A
    (continuousOn_matrix_spectrum _ A) (continuousOn_matrix_spectrum _ A)
  rw [← h1]
  have h2 : cfc (fun a : ℝ => (Real.sqrt a)⁻¹ * Real.sqrt a) A =
      cfc (fun _ : ℝ => (1 : ℝ)) A := by
    refine cfc_congr_of_eigenvalues hA.1 fun i => ?_
    have h3 : Real.sqrt (hA.1.eigenvalues i) ≠ 0 :=
      (Real.sqrt_pos.mpr (hA.eigenvalues_pos i)).ne'
    field_simp
  rw [h2]
  exact cfc_const_one ℝ A

/-- Lean implementation helper: `√A·(√A)⁻¹ = 1` for pd `A`. -/
lemma mul_posSqrt_inv (hA : A.PosDef) :
    posSqrt A * (posSqrt A)⁻¹ = 1 := by
  rw [posSqrt_inv_eq_cfc hA, posSqrt]
  have h1 := cfc_mul Real.sqrt (fun a : ℝ => (Real.sqrt a)⁻¹) A
    (continuousOn_matrix_spectrum _ A) (continuousOn_matrix_spectrum _ A)
  rw [← h1]
  have h2 : cfc (fun a : ℝ => Real.sqrt a * (Real.sqrt a)⁻¹) A =
      cfc (fun _ : ℝ => (1 : ℝ)) A := by
    refine cfc_congr_of_eigenvalues hA.1 fun i => ?_
    have h3 : Real.sqrt (hA.1.eigenvalues i) ≠ 0 :=
      (Real.sqrt_pos.mpr (hA.eigenvalues_pos i)).ne'
    field_simp
  rw [h2]
  exact cfc_const_one ℝ A

/-- Lean implementation helper: `√A⁻¹·A·√A⁻¹ = 1` for pd `A` — the
normalization used repeatedly in §8.4/§8.6. -/
lemma posSqrt_inv_conj_self (hA : A.PosDef) :
    (posSqrt A)⁻¹ * A * (posSqrt A)⁻¹ = 1 := by
  calc (posSqrt A)⁻¹ * A * (posSqrt A)⁻¹
      = (posSqrt A)⁻¹ * (posSqrt A * posSqrt A) * (posSqrt A)⁻¹ := by
        rw [posSqrt_mul_self hA.posSemidef]
    _ = ((posSqrt A)⁻¹ * posSqrt A) * (posSqrt A * (posSqrt A)⁻¹) := by
        noncomm_ring
    _ = 1 := by rw [posSqrt_inv_mul hA, mul_posSqrt_inv hA, Matrix.one_mul]

/-- Lean implementation helper: `A⁻¹·A = 1` for pd `A`. -/
lemma posDef_inv_mul_self (hA : A.PosDef) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)

/-- Lean implementation helper: `A·A⁻¹ = 1` for pd `A`. -/
lemma posDef_mul_inv_self (hA : A.PosDef) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)

/-- Lean implementation helper: `(√A)⁻¹` is a unit of the matrix ring. -/
lemma isUnit_posSqrt_inv (hA : A.PosDef) : IsUnit (posSqrt A)⁻¹ := by
  refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
  have h3 := congrArg Matrix.det (posSqrt_inv_mul hA)
  rw [Matrix.det_mul, Matrix.det_one] at h3
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h3)

/-- Lean implementation helper: conjugation by `(√H)⁻¹` (Hermitian) of a pd
matrix is pd — the normalization step in the book's §8.4.3 proof. -/
lemma posDef_posSqrt_inv_conj (hH : H.PosDef) (hA : A.PosDef) :
    ((posSqrt H)⁻¹ * A * (posSqrt H)⁻¹).PosDef := by
  have h1 : star ((posSqrt H)⁻¹) = (posSqrt H)⁻¹ := isHermitian_posSqrt_inv hH
  rw [show (posSqrt H)⁻¹ * A * (posSqrt H)⁻¹ =
    star ((posSqrt H)⁻¹) * A * (posSqrt H)⁻¹ by rw [h1]]
  exact ((isUnit_posSqrt_inv hH).posDef_star_left_conjugate_iff).mpr hA

end PosSqrt

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# §8.4.1–§8.4.4: The Logarithm of a Matrix — integral representation and
operator monotonicity

* **Proposition 8.4.1**  `log_eq_integral_inv` (scalar)
  and `matrix_log_eq_integral` (matrix) — the integral representation
  `log a = ∫₀^∞ [(1+u)⁻¹ − (a+u)⁻¹] du`.
* **Definition (operator monotone)**  `OperatorMonotoneOn`, indexed by the
  finite matrix dimension.
* **§8.4.2 bullet list**  `operatorMonotoneOn_affine`,
  `not_operatorMonotoneOn_sq`, `not_operatorMonotoneOn_exp`,
  `operatorMonotoneOn_smul`, `operatorMonotoneOn_add` (convex-cone closure).
* **Proposition 8.4.3**  `inv_shift_loewner_anti`
  (core), `neg_inv_shift_loewner_mono` (the book's displayed form),
  `operatorMonotoneOn_neg_inv_shift` (the book's "operator monotone on the
  positive real line" form).
* **Proposition 8.4.4**  `log_loewner_mono` and
  `operatorMonotoneOn_log`.
* Recovered implicit facts: `posSemidef_setIntegral` ("the semidefinite
  order is preserved by integration against a positive measure") and its
  Hermitian companion `isHermitian_setIntegral`.
-/

namespace MatrixConcentration

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A H M : Matrix n n ℂ}

/-- Lean implementation helper: any real function is continuous on a finite
set (companion to `continuousOn_matrix_spectrum`, for image sets in
`cfc_comp`). -/
lemma continuousOn_of_finite {s : Set ℝ} (hs : s.Finite) (f : ℝ → ℝ) :
    ContinuousOn f s := by
  rw [continuousOn_iff_continuous_restrict]
  haveI : DiscreteTopology s := by
    haveI : Finite s := hs
    infer_instance
  exact continuous_of_discreteTopology

/-! ## The scalar integral representation (Proposition 8.4.x, first half) -/

section ScalarIntegral

/-- Lean implementation helper.

The book's primitive `u ↦ log(1+u) − log(a+u)` from the proof of
Proposition 8.4.1. -/
private noncomputable def logPrim (a s : ℝ) : ℝ :=
  Real.log (1 + s) - Real.log (a + s)

/-- Lean implementation helper. -/
private lemma logPrim_hasDerivAt {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (logPrim a) ((1 + u)⁻¹ - (a + u)⁻¹) u := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 u := (hasDerivAt_id u).const_add 1
  have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) ((1 + u)⁻¹) u := by
    have h3 := (Real.hasDerivAt_log
      (show (1 : ℝ) + u ≠ 0 by positivity)).comp u h1
    simpa [Function.comp_def] using h3
  have h4 : HasDerivAt (fun s : ℝ => a + s) 1 u := (hasDerivAt_id u).const_add a
  have h5 : HasDerivAt (fun s : ℝ => Real.log (a + s)) ((a + u)⁻¹) u := by
    have h6 := (Real.hasDerivAt_log
      (show a + u ≠ 0 by positivity)).comp u h4
    simpa [Function.comp_def] using h6
  exact h2.sub h5

/-- Lean implementation helper. -/
private lemma logPrim_continuousWithinAt {a : ℝ} (ha : 0 < a) :
    ContinuousWithinAt (logPrim a) (Set.Ici 0) 0 := by
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : ContinuousAt (fun s : ℝ => Real.log (1 + s)) 0 := by
    have h2 : ContinuousAt (fun s : ℝ => 1 + s) 0 := by fun_prop
    have h3 := (Real.continuousAt_log
      (show (1 : ℝ) + 0 ≠ 0 by norm_num)).comp h2
    simpa [Function.comp_def] using h3
  have h4 : ContinuousAt (fun s : ℝ => Real.log (a + s)) 0 := by
    have h2 : ContinuousAt (fun s : ℝ => a + s) 0 := by fun_prop
    have h3 := (Real.continuousAt_log
      (show a + 0 ≠ 0 by simpa using ha.ne')).comp h2
    simpa [Function.comp_def] using h3
  exact h1.sub h4

/-- Lean implementation helper.

The book's boundary computation `lim_{L→∞} log((1+L)/(a+L)) = 0`. -/
private lemma logPrim_tendsto {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (logPrim a) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun s : ℝ => (1 + s) / (a + s))
      Filter.atTop (nhds 1) := by
    have h2 : (fun s : ℝ => (s⁻¹ + 1) / (a * s⁻¹ + 1)) =ᶠ[Filter.atTop]
        fun s : ℝ => (1 + s) / (a + s) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with s hs
      have h3 : a * s⁻¹ + 1 ≠ 0 := by positivity
      field_simp
    have h4 : Filter.Tendsto (fun s : ℝ => s⁻¹ + 1)
        Filter.atTop (nhds 1) := by
      simpa using tendsto_inv_atTop_zero.add
        (tendsto_const_nhds (x := (1 : ℝ)))
    have h5 : Filter.Tendsto (fun s : ℝ => a * s⁻¹ + 1)
        Filter.atTop (nhds 1) := by
      simpa using (tendsto_inv_atTop_zero.const_mul a).add
        (tendsto_const_nhds (x := (1 : ℝ)))
    have h6 := h4.div h5 one_ne_zero
    have h6' : Filter.Tendsto (fun s : ℝ => (s⁻¹ + 1) / (a * s⁻¹ + 1))
        Filter.atTop (nhds 1) := by
      simpa [Pi.div_def] using h6
    rw [Filter.tendsto_congr' h2] at h6'
    exact h6'
  have h7 : logPrim a =ᶠ[Filter.atTop]
      fun s => Real.log ((1 + s) / (a + s)) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with s hs
    rw [logPrim, Real.log_div (by linarith) (by linarith)]
  rw [Filter.tendsto_congr' h7]
  have h8 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
  simpa [Real.log_one, Function.comp_def] using h8

/-- Lean implementation helper: the integrand of 8.4.1 is
integrable on `(0, ∞)` (the book's improper integral converges); the sign
of the integrand is constant (`a ≥ 1` vs `a ≤ 1`). -/
lemma integrableOn_log_kernel {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => (1 + u)⁻¹ - (a + u)⁻¹) (Set.Ioi 0) := by
  rcases le_total 1 a with h1a | h1a
  · refine integrableOn_Ioi_deriv_of_nonneg (logPrim_continuousWithinAt ha)
      (fun u hu => logPrim_hasDerivAt ha (le_of_lt hu))
      (fun u hu => ?_) (logPrim_tendsto ha)
    have hu0 : (0 : ℝ) < u := hu
    have h2 : (a + u)⁻¹ ≤ (1 + u)⁻¹ := by
      have h3 : (0 : ℝ) < 1 + u := by linarith
      gcongr
    linarith
  · refine integrableOn_Ioi_deriv_of_nonpos (logPrim_continuousWithinAt ha)
      (fun u hu => logPrim_hasDerivAt ha (le_of_lt hu))
      (fun u hu => ?_) (logPrim_tendsto ha)
    have hu0 : (0 : ℝ) < u := hu
    have h2 : (1 + u)⁻¹ ≤ (a + u)⁻¹ := by
      have h3 : (0 : ℝ) < a + u := by linarith
      gcongr
    linarith

/-- **Book Proposition 8.4.1 (Integral Representation of the Logarithm), scalar half.**
The logarithm of a positive number `a` is given by
the integral `log a = ∫₀^∞ [1/(1+u) − 1/(a+u)] du`." -/
theorem log_eq_integral_inv {a : ℝ} (ha : 0 < a) :
    Real.log a = ∫ u in Set.Ioi (0 : ℝ), ((1 + u)⁻¹ - (a + u)⁻¹) := by
  have h1 := integral_Ioi_of_hasDerivAt_of_tendsto
    (logPrim_continuousWithinAt ha)
    (fun u hu => logPrim_hasDerivAt ha (le_of_lt hu))
    (integrableOn_log_kernel ha) (logPrim_tendsto ha)
  rw [h1]
  simp [logPrim, Real.log_one]

end ScalarIntegral

/-! ## Order and Hermitian structure pass through the Bochner integral

The book's implicit fact "the semidefinite order is preserved by
integration against a positive measure" (used in 8.4.4). -/

section IntegralOrder

/-- Lean implementation helper. -/
private noncomputable def quadFormCLM (x : n → ℂ) : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => star x ⬝ᵥ (M *ᵥ x)
      map_add' := fun M N => by simp [Matrix.add_mulVec]
      map_smul' := fun c M => by
        simp [Matrix.smul_mulVec, Complex.real_smul] }

/-- Lean implementation helper. -/
private lemma quadFormCLM_apply (x : n → ℂ) (M : Matrix n n ℂ) :
    quadFormCLM x M = star x ⬝ᵥ (M *ᵥ x) := rfl

/-- Lean implementation helper. -/
private noncomputable def conjTransposeCLM :
    Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Mᴴ
      map_add' := fun M N => Matrix.conjTranspose_add M N
      map_smul' := fun c M => by
        ext i j
        simp [Matrix.conjTranspose_apply] }

/-- Lean implementation helper. -/
private lemma conjTransposeCLM_apply (M : Matrix n n ℂ) :
    conjTransposeCLM (n := n) M = Mᴴ := rfl

/-- Lean implementation helper: a Bochner integral of Hermitian matrices is
Hermitian. -/
lemma isHermitian_setIntegral {F : ℝ → Matrix n n ℂ} {s : Set ℝ}
    (hs : MeasurableSet s) (hF : IntegrableOn F s)
    (hherm : ∀ u ∈ s, (F u).IsHermitian) :
    (∫ u in s, F u).IsHermitian := by
  show (∫ u in s, F u)ᴴ = ∫ u in s, F u
  have h1 := ContinuousLinearMap.integral_comp_comm conjTransposeCLM hF
  simp only [conjTransposeCLM_apply] at h1
  rw [← h1]
  exact setIntegral_congr_fun hs fun u hu => hherm u hu

/-- Lean implementation helper.

**Implicit fact (proof of 8.4.4)**  "the semidefinite
order is preserved by integration against a positive measure" — a Bochner
integral of psd matrices is psd. -/
lemma posSemidef_setIntegral {F : ℝ → Matrix n n ℂ} {s : Set ℝ}
    (hs : MeasurableSet s) (hF : IntegrableOn F s)
    (hpsd : ∀ u ∈ s, (F u).PosSemidef) :
    (∫ u in s, F u).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_setIntegral hs hF fun u hu => (hpsd u hu).1) fun x => ?_
  have h1 : star x ⬝ᵥ ((∫ u in s, F u) *ᵥ x) =
      ∫ u in s, star x ⬝ᵥ (F u *ᵥ x) := by
    have h2 := ContinuousLinearMap.integral_comp_comm (quadFormCLM x) hF
    simp only [quadFormCLM_apply] at h2
    exact h2.symm
  rw [h1]
  have hint : Integrable (fun u => star x ⬝ᵥ (F u *ᵥ x))
      (MeasureTheory.volume.restrict s) := by
    have h3 := (quadFormCLM (n := n) x).integrable_comp hF
    simpa only [quadFormCLM_apply] using h3
  rw [Complex.le_def]
  constructor
  · rw [Complex.zero_re]
    have h7 := integral_re hint
    simp only [RCLike.re_to_complex] at h7
    rw [← h7]
    refine setIntegral_nonneg hs fun u hu => ?_
    have h4 := (Complex.le_def.mp ((hpsd u hu).dotProduct_mulVec_nonneg x)).1
    simpa using h4
  · rw [Complex.zero_im]
    have h8 := integral_im hint
    simp only [RCLike.im_to_complex] at h8
    rw [← h8]
    have h5 : ∀ u ∈ s, (star x ⬝ᵥ (F u *ᵥ x)).im = 0 := fun u hu => by
      have h6 := (Complex.le_def.mp ((hpsd u hu).dotProduct_mulVec_nonneg x)).2
      simpa using h6.symm
    rw [setIntegral_congr_fun hs h5]
    simp

end IntegralOrder

/-! ## The matrix integral representation (Proposition 8.4.x, second half) -/

section MatrixIntegral

/-- Lean implementation helper.

The book's step "applying the scalar formula to each eigenvalue": the
matrix integrand decomposes over the eigenbasis of `A`. -/
private lemma matrix_log_kernel_eq (hA : A.PosDef) {u : ℝ}
    (hu : u ∈ Set.Ioi (0 : ℝ)) :
    (1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹ =
      ∑ j, ((((1 + u)⁻¹ - (hA.1.eigenvalues j + u)⁻¹ : ℝ)) : ℂ) •
        Matrix.vecMulVec (⇑(hA.1.eigenvectorBasis j))
          (star ⇑(hA.1.eigenvectorBasis j)) := by
  have hsa : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA.1
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  rw [inv_shift_eq_cfc hA hu0]
  have h1 : (1 + u)⁻¹ • (1 : Matrix n n ℂ) =
      cfc (fun _ : ℝ => (1 + u)⁻¹) A := by
    rw [cfc_const ((1 + u)⁻¹) A, Algebra.algebraMap_eq_smul_one]
  rw [h1]
  have h2 := cfc_sub (fun _ : ℝ => (1 + u)⁻¹) (fun a : ℝ => (a + u)⁻¹) A
    (continuousOn_matrix_spectrum _ A) (continuousOn_matrix_spectrum _ A)
  rw [← h2]
  exact cfc_eq_sum_outer hA.1 _

/-- Lean implementation helper: the matrix integrand of
8.4.1 is Bochner integrable on `(0, ∞)`. -/
lemma integrableOn_matrix_log_kernel (hA : A.PosDef) :
    IntegrableOn
      (fun u : ℝ => (1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹)
      (Set.Ioi 0) := by
  have h1 : IntegrableOn (fun u : ℝ =>
      ∑ j, ((((1 + u)⁻¹ - (hA.1.eigenvalues j + u)⁻¹ : ℝ)) : ℂ) •
        Matrix.vecMulVec (⇑(hA.1.eigenvectorBasis j))
          (star ⇑(hA.1.eigenvectorBasis j))) (Set.Ioi 0) := by
    refine integrable_finsetSum _ fun j _ => ?_
    exact ((integrableOn_log_kernel (hA.eigenvalues_pos j)).ofReal).smul_const _
  exact h1.congr_fun (fun u hu => (matrix_log_kernel_eq hA hu).symm)
    measurableSet_Ioi

/-- **Book Proposition 8.4.1 (Integral Representation of the Logarithm), matrix half.**
The logarithm of a positive-definite matrix `A` is
given by the integral `log A = ∫₀^∞ [(1+u)⁻¹ I − (A + uI)⁻¹] du`." -/
theorem matrix_log_eq_integral (hA : A.PosDef) :
    CFC.log A = ∫ u in Set.Ioi (0 : ℝ),
      ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹) := by
  have h0 : (∫ u in Set.Ioi (0 : ℝ),
      ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹)) =
      ∫ u in Set.Ioi (0 : ℝ),
        ∑ j, ((((1 + u)⁻¹ - (hA.1.eigenvalues j + u)⁻¹ : ℝ)) : ℂ) •
          Matrix.vecMulVec (⇑(hA.1.eigenvectorBasis j))
            (star ⇑(hA.1.eigenvectorBasis j)) :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun u hu => matrix_log_kernel_eq hA hu)
  have h2 : (∫ u in Set.Ioi (0 : ℝ),
      ∑ j, ((((1 + u)⁻¹ - (hA.1.eigenvalues j + u)⁻¹ : ℝ)) : ℂ) •
        Matrix.vecMulVec (⇑(hA.1.eigenvectorBasis j))
          (star ⇑(hA.1.eigenvectorBasis j))) =
      ∑ j, ∫ u in Set.Ioi (0 : ℝ),
        ((((1 + u)⁻¹ - (hA.1.eigenvalues j + u)⁻¹ : ℝ)) : ℂ) •
          Matrix.vecMulVec (⇑(hA.1.eigenvectorBasis j))
            (star ⇑(hA.1.eigenvectorBasis j)) :=
    integral_finsetSum _ fun j _ =>
      ((integrableOn_log_kernel (hA.eigenvalues_pos j)).ofReal).smul_const _
  have h1 : ∀ j, (∫ u in Set.Ioi (0 : ℝ),
      ((((1 + u)⁻¹ - (hA.1.eigenvalues j + u)⁻¹ : ℝ)) : ℂ) •
        Matrix.vecMulVec (⇑(hA.1.eigenvectorBasis j))
          (star ⇑(hA.1.eigenvectorBasis j))) =
      ((Real.log (hA.1.eigenvalues j) : ℝ) : ℂ) •
        Matrix.vecMulVec (⇑(hA.1.eigenvectorBasis j))
          (star ⇑(hA.1.eigenvectorBasis j)) := by
    intro j
    rw [integral_smul_const]
    congr 1
    rw [integral_complex_ofReal,
      ← log_eq_integral_inv (hA.eigenvalues_pos j)]
  rw [h0, h2, Finset.sum_congr rfl fun j _ => h1 j]
  exact cfc_eq_sum_outer hA.1 Real.log

end MatrixIntegral

/-! ## Operator monotone functions (§8.4.2) -/

section OperatorMonotone

/-- **Book §8.4.2 (definition of operator monotonicity).** A function `f : I → ℝ` is operator
monotone on `I` when `A ≼ H` implies `f(A) ≼ f(H)` for all Hermitian
matrices `A` and `H` whose eigenvalues are contained in `I` — rendered at
each square-matrix index type `n`. -/
def OperatorMonotoneOn (n : Type*) [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian),
    (∀ i, hA.eigenvalues i ∈ I) → (∀ i, hH.eigenvalues i ∈ I) →
      A ≤ H → cfc f A ≤ cfc f H

/-- Lean implementation helper: `cfc` of an affine function. -/
lemma cfc_affine_eq (hA : A.IsHermitian) (α β : ℝ) :
    cfc (fun t : ℝ => α + β * t) A = α • (1 : Matrix n n ℂ) + β • A := by
  have hsa : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  have h1 := cfc_add (a := A) (fun _ : ℝ => α) (fun t : ℝ => β * t)
    (continuousOn_matrix_spectrum _ A) (continuousOn_matrix_spectrum _ A)
  rw [show (fun t : ℝ => α + β * t) =
    fun t : ℝ => (fun _ : ℝ => α) t + (fun t : ℝ => β * t) t from rfl, h1,
    cfc_const α A, cfc_const_mul_id β A, Algebra.algebraMap_eq_smul_one]

/-- **Book §8.4.2, bullet 1**  "When `β ≥ 0`, the weakly increasing affine
function `t ↦ α + βt` is operator monotone on each interval `I` of the real
line." -/
theorem operatorMonotoneOn_affine (n : Type*) [Fintype n] [DecidableEq n]
    {α β : ℝ} (hβ : 0 ≤ β) (I : Set ℝ) :
    OperatorMonotoneOn n (fun t => α + β * t) I := by
  intro A H hA hH _ _ hle
  rw [cfc_affine_eq hA α β, cfc_affine_eq hH α β]
  exact add_le_add_right (smul_loewner_mono hβ hle) _

/-- **Book §8.4.2, bullet 4**  "When `α ≥ 0` and `f` is operator monotone on
`I`, the function `αf` is operator monotone on `I`." -/
theorem operatorMonotoneOn_smul {f : ℝ → ℝ} {I : Set ℝ} {α : ℝ}
    (hα : 0 ≤ α) (hf : OperatorMonotoneOn n f I) :
    OperatorMonotoneOn n (fun t => α * f t) I := by
  intro A H hA hH hAI hHI hle
  rw [cfc_const_mul α f A (continuousOn_matrix_spectrum _ A),
    cfc_const_mul α f H (continuousOn_matrix_spectrum _ H)]
  exact smul_loewner_mono hα (hf A H hA hH hAI hHI hle)

/-- **Book §8.4.2, bullet 5**  "If `f` and `g` are operator monotone on an
interval `I`, then `f + g` is operator monotone on `I`."  Together with the
previous bullet: "the operator monotone functions form a convex cone." -/
theorem operatorMonotoneOn_add {f g : ℝ → ℝ} {I : Set ℝ}
    (hf : OperatorMonotoneOn n f I) (hg : OperatorMonotoneOn n g I) :
    OperatorMonotoneOn n (fun t => f t + g t) I := by
  intro A H hA hH hAI hHI hle
  rw [cfc_add (a := A) f g (continuousOn_matrix_spectrum _ A)
      (continuousOn_matrix_spectrum _ A),
    cfc_add (a := H) f g (continuousOn_matrix_spectrum _ H)
      (continuousOn_matrix_spectrum _ H)]
  exact add_le_add (hf A H hA hH hAI hHI hle) (hg A H hA hH hAI hHI hle)

end OperatorMonotone

/-! ## The negative inverse is operator monotone (§8.4.3) -/

section InverseMonotone

/-- Lean implementation helper.

Lean implementation core of **Proposition (8.4.3)** 
`A ≼ H` implies `(H + uI)⁻¹ ≼ (A + uI)⁻¹` for pd `A, H` and `u ≥ 0` —
the book's proof via two applications of the Conjugation Rule. -/
theorem inv_shift_loewner_anti {u : ℝ} (hu : 0 ≤ u)
    (hA : A.PosDef) (hH : H.PosDef) (hle : A ≤ H) :
    (H + u • (1 : Matrix n n ℂ))⁻¹ ≤ (A + u • 1)⁻¹ := by
  set Au := A + u • (1 : Matrix n n ℂ) with hAu
  set Hu := H + u • (1 : Matrix n n ℂ) with hHu
  have hAupd : Au.PosDef := posDef_add_smul_one hA hu
  have hHupd : Hu.PosDef := posDef_add_smul_one hH hu
  have hle_u : Au ≤ Hu := by
    rw [hAu, hHu]
    exact add_le_add_left hle _
  set S := (posSqrt Hu)⁻¹ with hS
  have hSh : S.IsHermitian := isHermitian_posSqrt_inv hHupd
  -- Step 1 (book): `0 ≺ Hu^{-1/2} Au Hu^{-1/2} ≼ I` by the Conjugation Rule
  have h1 : S * Au * S ≤ 1 := by
    have h2 := conjugation_rule hle_u S
    rw [hSh.eq] at h2
    calc S * Au * S ≤ S * Hu * S := h2
      _ = 1 := posSqrt_inv_conj_self hHupd
  have h3 : (S * Au * S).PosDef := posDef_posSqrt_inv_conj hHupd hAupd
  -- Step 2 (book): eigenvalues ≤ 1 invert to eigenvalues ≥ 1, and
  -- `(Hu^{-1/2} Au Hu^{-1/2})⁻¹ = Hu^{1/2} Au⁻¹ Hu^{1/2}`
  have h4 : (1 : Matrix n n ℂ) ≤ posSqrt Hu * Au⁻¹ * posSqrt Hu := by
    have h5 := one_le_inv_of_le_one h3 h1
    have h6 : (S * Au * S)⁻¹ = posSqrt Hu * Au⁻¹ * posSqrt Hu := by
      refine Matrix.inv_eq_left_inv ?_
      calc (posSqrt Hu * Au⁻¹ * posSqrt Hu) * (S * Au * S)
          = posSqrt Hu * Au⁻¹ * (posSqrt Hu * S) * (Au * S) := by
            noncomm_ring
        _ = posSqrt Hu * Au⁻¹ * (Au * S) := by
            rw [hS, mul_posSqrt_inv hHupd, Matrix.mul_one]
        _ = posSqrt Hu * (Au⁻¹ * Au) * S := by noncomm_ring
        _ = posSqrt Hu * S := by
            rw [posDef_inv_mul_self hAupd, Matrix.mul_one]
        _ = 1 := by rw [hS, mul_posSqrt_inv hHupd]
    rwa [h6] at h5
  -- Step 3 (book): conjugate back by `Hu^{-1/2}`
  have h7 := conjugation_rule h4 S
  rw [hSh.eq] at h7
  have h8 : S * (1 : Matrix n n ℂ) * S = Hu⁻¹ := by
    rw [Matrix.mul_one, hS, ← Matrix.mul_inv_rev,
      posSqrt_mul_self hHupd.posSemidef]
  have h9 : S * (posSqrt Hu * Au⁻¹ * posSqrt Hu) * S = Au⁻¹ := by
    calc S * (posSqrt Hu * Au⁻¹ * posSqrt Hu) * S
        = (S * posSqrt Hu) * Au⁻¹ * (posSqrt Hu * S) := by noncomm_ring
      _ = Au⁻¹ := by
          rw [hS, posSqrt_inv_mul hHupd, mul_posSqrt_inv hHupd,
            Matrix.one_mul, Matrix.mul_one]
  rwa [h8, h9] at h7

/-- **Book Proposition (Negative Inverse is Operator Monotone,
8.4.3), displayed form**  "for positive-definite matrices `A`
and `H`, `A ≼ H` implies `−(A + uI)⁻¹ ≼ −(H + uI)⁻¹`." -/
theorem neg_inv_shift_loewner_mono {u : ℝ} (hu : 0 ≤ u)
    (hA : A.PosDef) (hH : H.PosDef) (hle : A ≤ H) :
    -(A + u • (1 : Matrix n n ℂ))⁻¹ ≤ -(H + u • 1)⁻¹ :=
  neg_le_neg (inv_shift_loewner_anti hu hA hH hle)

/-- **Book Proposition 8.4.3, abstract form**  "For each number
`u ≥ 0`, the function `a ↦ −(a+u)⁻¹` is operator monotone on the positive
real line." -/
theorem operatorMonotoneOn_neg_inv_shift (n : Type*) [Fintype n]
    [DecidableEq n] {u : ℝ} (hu : 0 ≤ u) :
    OperatorMonotoneOn n (fun a => -(a + u)⁻¹) (Set.Ioi 0) := by
  intro A H hA hH hAI hHI hle
  have hApd : A.PosDef :=
    posDef_iff_exists_eigenvalues_pos.mpr ⟨hA, fun i => hAI i⟩
  have hHpd : H.PosDef :=
    posDef_iff_exists_eigenvalues_pos.mpr ⟨hH, fun i => hHI i⟩
  have hkey : ∀ (M : Matrix n n ℂ) (hM : M.PosDef),
      cfc (fun a : ℝ => -(a + u)⁻¹) M = -(M + u • 1)⁻¹ := by
    intro M hM
    have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM.1
    rw [show (fun a : ℝ => -(a + u)⁻¹) =
      fun a : ℝ => -((fun a : ℝ => (a + u)⁻¹) a) from rfl, cfc_neg,
      ← inv_shift_eq_cfc hM hu]
  rw [hkey A hApd, hkey H hHpd]
  exact neg_inv_shift_loewner_mono hu hApd hHpd hle

end InverseMonotone

/-! ## The logarithm is operator monotone (§8.4.4) -/

section LogMonotone

/-- **Book Proposition (Logarithm is Operator Monotone, 8.4.4),
displayed form**  "for positive-definite matrices `A` and `H`, `A ≼ H`
implies `log A ≼ log H`" — via the integral representation, the
monotonicity of the negative inverse, and preservation of the semidefinite
order under integration. -/
theorem log_loewner_mono' (hA : A.PosDef) (hH : H.PosDef) (hle : A ≤ H) :
    CFC.log A ≤ CFC.log H := by
  rw [Matrix.le_iff]
  have h1 : CFC.log H - CFC.log A = ∫ u in Set.Ioi (0 : ℝ),
      (((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (H + u • 1)⁻¹) -
        ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹)) := by
    rw [integral_sub (integrableOn_matrix_log_kernel hH)
      (integrableOn_matrix_log_kernel hA), ← matrix_log_eq_integral hA,
      ← matrix_log_eq_integral hH]
  rw [h1]
  refine posSemidef_setIntegral measurableSet_Ioi
    ((integrableOn_matrix_log_kernel hH).sub
      (integrableOn_matrix_log_kernel hA)) fun u hu => ?_
  have h2 : ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (H + u • 1)⁻¹) -
      ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹) =
      (A + u • 1)⁻¹ - (H + u • 1)⁻¹ := by abel
  rw [h2, ← Matrix.le_iff]
  exact inv_shift_loewner_anti (le_of_lt hu) hA hH hle

/-- **Book Proposition 8.4.4, abstract form**  "The logarithm is
an operator monotone function on the positive real line." -/
theorem operatorMonotoneOn_log (n : Type*) [Fintype n] [DecidableEq n] :
    OperatorMonotoneOn n Real.log (Set.Ioi 0) := by
  intro A H hA hH hAI hHI hle
  exact log_loewner_mono' (posDef_iff_exists_eigenvalues_pos.mpr
    ⟨hA, fun i => hAI i⟩)
    (posDef_iff_exists_eigenvalues_pos.mpr ⟨hH, fun i => hHI i⟩) hle

end LogMonotone

/-! ## The two negative examples (§8.4.2, bullets 2–3) -/

section Counterexamples

/-- Lean implementation helper.

The counterexample pair: `ceA = [[2,1],[1,2]]`, `ceH = [[3,1],[1,2]]`
(the book's classical `t²` counterexample, shifted into the pd cone). -/
private noncomputable def ceA : Matrix (Fin 2) (Fin 2) ℂ := !![2, 1; 1, 2]

/-- Lean implementation helper. -/
private noncomputable def ceH : Matrix (Fin 2) (Fin 2) ℂ := !![3, 1; 1, 2]

/-- Lean implementation helper. -/
private lemma ceA_posDef : ceA.PosDef := by
  have h1 : (!![(1 : ℂ), 1; 0, 0])ᴴ * !![(1 : ℂ), 1; 0, 0] =
      !![(1 : ℂ), 1; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  have h2 : (!![(1 : ℂ), 1; 1, 1]).PosSemidef :=
    h1 ▸ Matrix.posSemidef_conjTranspose_mul_self _
  have h3 : ceA = 1 + !![(1 : ℂ), 1; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ceA, Matrix.one_apply]
  rw [h3]
  exact Matrix.PosDef.add_posSemidef Matrix.PosDef.one h2

/-- Lean implementation helper. -/
private lemma ceD_posSemidef : (!![(1 : ℂ), 0; 0, 0]).PosSemidef := by
  have h1 : (!![(1 : ℂ), 0; 0, 0])ᴴ * !![(1 : ℂ), 0; 0, 0] =
      !![(1 : ℂ), 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  exact h1 ▸ Matrix.posSemidef_conjTranspose_mul_self _

/-- Lean implementation helper. -/
private lemma ceH_posDef : ceH.PosDef := by
  have h1 : ceH = ceA + !![(1 : ℂ), 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [ceA, ceH]
  rw [h1]
  exact ceA_posDef.add_posSemidef ceD_posSemidef

/-- Lean implementation helper. -/
private lemma ceA_le_ceH : ceA ≤ ceH := by
  rw [Matrix.le_iff]
  have h1 : ceH - ceA = !![(1 : ℂ), 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [ceA, ceH, Matrix.sub_apply]
  rw [h1]
  exact ceD_posSemidef

/-- Lean implementation helper.

The failure of the squared order: the quadratic form of
`ceH² − ceA² = [[5,1],[1,0]]` at `x = (1,−6)` equals `−7 < 0`. -/
private lemma ce_sq_not_le : ¬ (ceA * ceA ≤ ceH * ceH) := by
  intro hc
  have h3 := (Matrix.le_iff.mp hc).dotProduct_mulVec_nonneg ![(1 : ℂ), -6]
  have hval : star ![(1 : ℂ), -6] ⬝ᵥ
      ((ceH * ceH - ceA * ceA) *ᵥ ![(1 : ℂ), -6]) = -7 := by
    simp [ceA, ceH, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.sub_apply, Complex.conj_ofNat]
    norm_num
  rw [hval] at h3
  have h4 := (Complex.le_def.mp h3).1
  norm_num at h4

/-- Lean implementation helper: `cfc` of `t ↦ t²` is the matrix square. -/
lemma cfc_sq_eq (hM : M.IsHermitian) :
    cfc (fun t : ℝ => t ^ 2) M = M * M := by
  have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  have h1 := cfc_mul (id : ℝ → ℝ) (id : ℝ → ℝ) M
    (continuousOn_matrix_spectrum _ M) (continuousOn_matrix_spectrum _ M)
  rw [show (fun t : ℝ => t ^ 2) = fun t : ℝ => id t * id t by
    funext t; simp [sq], h1, cfc_id ℝ M]

/-- **Book §8.4.2, bullet 2**  "The quadratic function `t ↦ t²` is **not**
operator monotone on the positive real line."  Witness:
`[[2,1],[1,2]] ≼ [[3,1],[1,2]]` but the squares are not comparable
(quadratic form at `(1,−6)` equals `−7`). -/
theorem not_operatorMonotoneOn_sq :
    ¬ OperatorMonotoneOn (Fin 2) (fun t => t ^ 2) (Set.Ioi 0) := by
  intro hmono
  have h1 := hmono ceA ceH ceA_posDef.1 ceH_posDef.1
    (fun i => ceA_posDef.eigenvalues_pos i)
    (fun i => ceH_posDef.eigenvalues_pos i) ceA_le_ceH
  rw [cfc_sq_eq ceA_posDef.1, cfc_sq_eq ceH_posDef.1] at h1
  exact ce_sq_not_le h1

/-- **Book §8.4.2, bullet 3**  "The exponential map `t ↦ e^t` is **not**
operator monotone on the real line."  Book's remark, recovered proof: if
`exp` were operator monotone then applying it to
`2·log ceA ≼ 2·log ceH` (from 8.4.4) would give
`ceA² ≼ ceH²`, contradicting the previous bullet's computation. -/
theorem not_operatorMonotoneOn_exp :
    ¬ OperatorMonotoneOn (Fin 2) Real.exp Set.univ := by
  intro hmono
  have hlog : cfc (fun t : ℝ => 2 * Real.log t) ceA ≤
      cfc (fun t : ℝ => 2 * Real.log t) ceH := by
    rw [cfc_const_mul 2 Real.log ceA (continuousOn_matrix_spectrum _ _),
      cfc_const_mul 2 Real.log ceH (continuousOn_matrix_spectrum _ _)]
    exact smul_loewner_mono (by norm_num)
      (log_loewner_mono' ceA_posDef ceH_posDef ceA_le_ceH)
  have h1 := hmono _ _ (isHermitian_cfc _ _) (isHermitian_cfc _ _)
    (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) hlog
  have hkey : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosDef),
      cfc Real.exp (cfc (fun t : ℝ => 2 * Real.log t) M) = M * M := by
    intro M hM
    have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM.1
    rw [← cfc_comp Real.exp (fun t : ℝ => 2 * Real.log t) M hsa
      (continuousOn_of_finite (Matrix.finite_real_spectrum.image _) _)
      (continuousOn_matrix_spectrum _ M)]
    have h2 : cfc (Real.exp ∘ fun t : ℝ => 2 * Real.log t) M =
        cfc (fun t : ℝ => t ^ 2) M := by
      refine cfc_congr_of_eigenvalues hM.1 fun i => ?_
      have hpos := hM.eigenvalues_pos i
      simp only [Function.comp_apply]
      rw [two_mul, Real.exp_add, Real.exp_log hpos, sq]
    rw [h2, cfc_sq_eq hM.1]
  rw [hkey ceA ceA_posDef, hkey ceH ceH_posDef] at h1
  exact ce_sq_not_le h1

end Counterexamples

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# §8.4.5–§8.4.8: Operator convexity and the logarithm

* **Definition (Operator Convex Function, 8.4.5)** 
  `OperatorConvexOn`, `OperatorConcaveOn`, indexed by finite matrix
  dimension; "a function `g` is operator concave when `−g` is
  operator convex" is rendered literally.
* **§8.4.5 bullet list**  `operatorConvexOn_quadratic`,
  `not_operatorConvexOn_exp`, `operatorConvexOn_smul`,
  `operatorConvexOn_add` (convex-cone closure).  The failure of operator
  convexity for `e^t` is certified by an exact `2 × 2` counterexample.
* **Fact (Schur Complements, 8.4.7)** 
  `schur_complement_posSemidef_iff` (correspondence to Mathlib's
  `Matrix.PosSemidef.fromBlocks₁₁`) and the display (8.4.6)
  `posSemidef_fromBlocks_one_inv`: `0 ≼ [[T, I], [I, T⁻¹]]`.
* **Proposition (Inverse is Operator Convex, 8.4.6)** 
  `inv_shift_operator_convex` (displayed form),
  `operatorConvexOn_inv_shift` (abstract form).
* **Proposition (Logarithm is Operator Concave, 8.4.8)** 
  `log_operator_concave` (displayed form), `operatorConcaveOn_log`
  (abstract form).  (Mathlib's `CFC.concaveOn_log` is a related scalar-CFC
  statement; the versions here are the book's, proved by the book's
  integral route.)
-/

namespace MatrixConcentration

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A H M T : Matrix n n ℂ}

/-! ## Operator convex functions (§8.4.5) -/

section OperatorConvexDef

/-- **Book Definition (Operator Convex Function, 8.4.5)** 
"`f : I → ℝ` is operator convex on `I` when
`f(τA + τ̄H) ≼ τ·f(A) + τ̄·f(H)` for all `τ ∈ [0,1]` and for all Hermitian
matrices `A` and `H` whose eigenvalues are contained in `I`" — rendered at
each square-matrix index type `n`. -/
def OperatorConvexOn (n : Type*) [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian),
    (∀ i, hA.eigenvalues i ∈ I) → (∀ i, hH.eigenvalues i ∈ I) →
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      cfc f (τ • A + (1 - τ) • H) ≤ τ • cfc f A + (1 - τ) • cfc f H

/-- **Book Definition 8.4.5, second half**  "A function
`g : I → ℝ` is operator concave when `−g` is operator convex on `I`." -/
def OperatorConcaveOn (n : Type*) [Fintype n] [DecidableEq n]
    (g : ℝ → ℝ) (I : Set ℝ) : Prop :=
  OperatorConvexOn n (fun t => -(g t)) I

/-- Lean implementation helper: a real convex combination of Hermitian
matrices is Hermitian. -/
lemma isHermitian_convex_combo (hA : A.IsHermitian) (hH : H.IsHermitian)
    (τ : ℝ) : (τ • A + (1 - τ) • H).IsHermitian := by
  show (τ • A + (1 - τ) • H)ᴴ = _
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, hA.eq, hH.eq, star_trivial, star_trivial]

/-- Lean implementation helper: the convexity defect of the matrix square,
`τ·A² + τ̄·H² − (τA + τ̄H)² = ττ̄·(A−H)²` (the algebra behind §8.4.5,
bullet 1). -/
lemma sq_convex_combo_diff (A H : Matrix n n ℂ) (τ : ℝ) :
    τ • (A * A) + (1 - τ) • (H * H) -
      (τ • A + (1 - τ) • H) * (τ • A + (1 - τ) • H) =
      (τ * (1 - τ)) • ((A - H) * (A - H)) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    smul_mul_assoc, mul_smul_comm]
  module

/-- **Book §8.4.5, bullet 1**  "When `γ ≥ 0`, the quadratic function
`t ↦ α + βt + γt²` is operator convex on the real line." -/
theorem operatorConvexOn_quadratic (n : Type*) [Fintype n] [DecidableEq n]
    {α β γ : ℝ} (hγ : 0 ≤ γ) :
    OperatorConvexOn n (fun t => α + β * t + γ * t ^ 2) Set.univ := by
  intro A H hA hH _ _ τ hτ
  have hkey : ∀ (M : Matrix n n ℂ) (hM : M.IsHermitian),
      cfc (fun t : ℝ => α + β * t + γ * t ^ 2) M =
        (α • (1 : Matrix n n ℂ) + β • M) + γ • (M * M) := by
    intro M hM
    have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
    have h1 := cfc_add (a := M) (fun t : ℝ => α + β * t)
      (fun t : ℝ => γ * t ^ 2) (continuousOn_matrix_spectrum _ M)
      (continuousOn_matrix_spectrum _ M)
    rw [show (fun t : ℝ => α + β * t + γ * t ^ 2) =
      fun t : ℝ => (fun t : ℝ => α + β * t) t + (fun t : ℝ => γ * t ^ 2) t
      from rfl, h1, cfc_affine_eq hM,
      cfc_const_mul γ (fun t : ℝ => t ^ 2) M
        (continuousOn_matrix_spectrum _ M), cfc_sq_eq hM]
  rw [hkey _ (isHermitian_convex_combo hA hH τ), hkey A hA, hkey H hH,
    Matrix.le_iff]
  have hdiff : (τ • ((α • (1 : Matrix n n ℂ) + β • A) + γ • (A * A)) +
      (1 - τ) • ((α • (1 : Matrix n n ℂ) + β • H) + γ • (H * H))) -
      ((α • (1 : Matrix n n ℂ) + β • (τ • A + (1 - τ) • H)) +
        γ • ((τ • A + (1 - τ) • H) * (τ • A + (1 - τ) • H))) =
      γ • (τ • (A * A) + (1 - τ) • (H * H) -
        (τ • A + (1 - τ) • H) * (τ • A + (1 - τ) • H)) := by
    module
  rw [hdiff, sq_convex_combo_diff A H τ, smul_smul]
  refine posSemidef_smul_nonneg (posSemidef_sq (hA.sub hH)) ?_
  have h2 : 0 ≤ τ * (1 - τ) := mul_nonneg hτ.1 (by linarith [hτ.2])
  positivity

/-- **Book §8.4.5, bullet 3**  "When `α ≥ 0` and `f` is operator convex on `I`,
the function `αf` is operator convex in `I`." -/
theorem operatorConvexOn_smul {f : ℝ → ℝ} {I : Set ℝ} {α : ℝ}
    (hα : 0 ≤ α) (hf : OperatorConvexOn n f I) :
    OperatorConvexOn n (fun t => α * f t) I := by
  intro A H hA hH hAI hHI τ hτ
  rw [cfc_const_mul α f _ (continuousOn_matrix_spectrum _ _),
    cfc_const_mul α f A (continuousOn_matrix_spectrum _ A),
    cfc_const_mul α f H (continuousOn_matrix_spectrum _ H)]
  have h1 := smul_loewner_mono hα (hf A H hA hH hAI hHI τ hτ)
  rw [smul_add, smul_smul, smul_smul, mul_comm α τ, mul_comm α (1 - τ),
    ← smul_smul, ← smul_smul] at h1
  exact h1

/-- **Book §8.4.5, bullet 4**  "If `f` and `g` are operator convex on `I`, then
`f + g` is operator convex on `I`."  Together with the previous bullet, the
operator convex functions on `I` form a convex cone (the source misprints
this closing remark as "the operator *monotone* functions form a convex
cone"; see SI-C8-3). -/
theorem operatorConvexOn_add {f g : ℝ → ℝ} {I : Set ℝ}
    (hf : OperatorConvexOn n f I) (hg : OperatorConvexOn n g I) :
    OperatorConvexOn n (fun t => f t + g t) I := by
  intro A H hA hH hAI hHI τ hτ
  rw [cfc_add (a := τ • A + (1 - τ) • H) f g
      (continuousOn_matrix_spectrum _ _) (continuousOn_matrix_spectrum _ _),
    cfc_add (a := A) f g (continuousOn_matrix_spectrum _ A)
      (continuousOn_matrix_spectrum _ A),
    cfc_add (a := H) f g (continuousOn_matrix_spectrum _ H)
      (continuousOn_matrix_spectrum _ H)]
  have h1 := add_le_add (hf A H hA hH hAI hHI τ hτ) (hg A H hA hH hAI hHI τ hτ)
  calc cfc f (τ • A + (1 - τ) • H) + cfc g (τ • A + (1 - τ) • H)
      ≤ (τ • cfc f A + (1 - τ) • cfc f H) +
        (τ • cfc g A + (1 - τ) • cfc g H) := h1
    _ = τ • (cfc f A + cfc g A) + (1 - τ) • (cfc f H + cfc g H) := by
        module

/-! ### The exponential is not operator convex (§8.4.5, bullet 2) -/

/-- Lean implementation helper: first integer matrix in the exact exponential
counterexample.  Its eigenvalues are `1` and `-4`. -/
private noncomputable def b01A0 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 2; 2, -3]

/-- Lean implementation helper: second integer matrix in the exact exponential
counterexample.  Its eigenvalues are `4` and `-1`. -/
private noncomputable def b01H0 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 2; 2, 3]

/-- Lean implementation helper: midpoint of `b01A0` and `b01H0`; its
eigenvalues are `2` and `-2`. -/
private noncomputable def b01M0 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 2; 2, 0]

/-- Lean implementation helper. -/
private noncomputable def b01A : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.log 2) • b01A0

/-- Lean implementation helper. -/
private noncomputable def b01H : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.log 2) • b01H0

/-- Lean implementation helper. -/
private noncomputable def b01M : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.log 2) • b01M0

private lemma b01A_hermitian : b01A.IsHermitian := by
  have hstar : star (Complex.log 2) = Complex.log 2 := by
    have hlog_eq : (Real.log 2 : ℂ) = Complex.log 2 := by
      convert Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2) using 1
      all_goals norm_num
    rw [← hlog_eq]
    exact Complex.conj_ofReal _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b01A, b01A0, Matrix.conjTranspose_apply, hstar]

private lemma b01H_hermitian : b01H.IsHermitian := by
  have hstar : star (Complex.log 2) = Complex.log 2 := by
    have hlog_eq : (Real.log 2 : ℂ) = Complex.log 2 := by
      convert Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2) using 1
      all_goals norm_num
    rw [← hlog_eq]
    exact Complex.conj_ofReal _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b01H, b01H0, Matrix.conjTranspose_apply, hstar]

private lemma b01M_hermitian : b01M.IsHermitian := by
  have hstar : star (Complex.log 2) = Complex.log 2 := by
    have hlog_eq : (Real.log 2 : ℂ) = Complex.log 2 := by
      convert Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2) using 1
      all_goals norm_num
    rw [← hlog_eq]
    exact Complex.conj_ofReal _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b01M, b01M0, Matrix.conjTranspose_apply, hstar]

private lemma b01A_spectrum :
    spectrum ℝ b01A ⊆ {Real.log 2, -4 * Real.log 2} := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hxC : (x : ℂ) ∈ spectrum ℂ b01A := spectrum.algebraMap_mem ℂ hx
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_ne_iff] at hxC
  have hdet : x * (x + 3 * Real.log 2) - 4 * (Real.log 2) ^ 2 = 0 := by
    apply Complex.ofReal_injective
    norm_num [Matrix.det_fin_two, b01A, b01A0, Matrix.algebraMap_eq_diagonal,
      Pi.algebraMap_def, Matrix.diagonal_apply] at hxC ⊢
    ring_nf at hxC ⊢
    exact hxC
  have hpoly : (x - Real.log 2) * (x + 4 * Real.log 2) = 0 := by
    calc
      _ = x * (x + 3 * Real.log 2) - 4 * (Real.log 2) ^ 2 := by ring
      _ = 0 := hdet
  rcases mul_eq_zero.mp hpoly with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by linarith)

private lemma b01H_spectrum :
    spectrum ℝ b01H ⊆ {4 * Real.log 2, -Real.log 2} := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hxC : (x : ℂ) ∈ spectrum ℂ b01H := spectrum.algebraMap_mem ℂ hx
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_ne_iff] at hxC
  have hdet : x * (x - 3 * Real.log 2) - 4 * (Real.log 2) ^ 2 = 0 := by
    apply Complex.ofReal_injective
    norm_num [Matrix.det_fin_two, b01H, b01H0, Matrix.algebraMap_eq_diagonal,
      Pi.algebraMap_def, Matrix.diagonal_apply] at hxC ⊢
    ring_nf at hxC ⊢
    exact hxC
  have hpoly : (x - 4 * Real.log 2) * (x + Real.log 2) = 0 := by
    calc
      _ = x * (x - 3 * Real.log 2) - 4 * (Real.log 2) ^ 2 := by ring
      _ = 0 := hdet
  rcases mul_eq_zero.mp hpoly with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by linarith)

private lemma b01M_spectrum :
    spectrum ℝ b01M ⊆ {2 * Real.log 2, -2 * Real.log 2} := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hxC : (x : ℂ) ∈ spectrum ℂ b01M := spectrum.algebraMap_mem ℂ hx
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_ne_iff] at hxC
  have hdet : x ^ 2 - 4 * (Real.log 2) ^ 2 = 0 := by
    apply Complex.ofReal_injective
    norm_num [Matrix.det_fin_two, b01M, b01M0, Matrix.algebraMap_eq_diagonal,
      Pi.algebraMap_def, Matrix.diagonal_apply] at hxC ⊢
    ring_nf at hxC ⊢
    exact hxC
  have hpoly : (x - 2 * Real.log 2) * (x + 2 * Real.log 2) = 0 := by
    calc
      _ = x ^ 2 - 4 * (Real.log 2) ^ 2 := by ring
      _ = 0 := hdet
  rcases mul_eq_zero.mp hpoly with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by linarith)

private lemma b01_exp_log_two : Real.exp (Real.log 2) = 2 := by
  rw [Real.exp_log (by norm_num)]

private lemma b01_exp_four_log_two : Real.exp (4 * Real.log 2) = 16 := by
  rw [show 4 * Real.log 2 =
      Real.log 2 + Real.log 2 + Real.log 2 + Real.log 2 by ring,
    Real.exp_add, Real.exp_add, Real.exp_add, b01_exp_log_two]
  norm_num

private lemma b01_exp_neg_log_two : Real.exp (-Real.log 2) = 1 / 2 := by
  rw [Real.exp_neg, b01_exp_log_two]
  norm_num

private lemma b01_exp_neg_four_log_two :
    Real.exp (-4 * Real.log 2) = 1 / 16 := by
  rw [show -4 * Real.log 2 = -(4 * Real.log 2) by ring,
    Real.exp_neg, b01_exp_four_log_two]
  norm_num

private lemma b01_exp_two_log_two : Real.exp (2 * Real.log 2) = 4 := by
  rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring,
    Real.exp_add, b01_exp_log_two]
  norm_num

private lemma b01_exp_neg_two_log_two :
    Real.exp (-2 * Real.log 2) = 1 / 4 := by
  rw [show -2 * Real.log 2 = -(2 * Real.log 2) by ring,
    Real.exp_neg, b01_exp_two_log_two]
  norm_num

private lemma b01_cfc_A :
    cfc Real.exp b01A = !![(129 / 80 : ℂ), 31 / 40; 31 / 40, 9 / 20] := by
  have hlog : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hlogC : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
  have hlog_eq : (Real.log 2 : ℂ) = Complex.log 2 := by
    convert Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2) using 1
    all_goals norm_num
  calc
    cfc Real.exp b01A =
        cfc (fun x : ℝ => (31 / 80) * (x / Real.log 2) + 129 / 80) b01A := by
      apply cfc_congr
      intro x hx
      rcases b01A_spectrum hx with h | h
      · subst x
        rw [b01_exp_log_two]
        field_simp
        norm_num
      · subst x
        rw [b01_exp_neg_four_log_two]
        field_simp
        ring
    _ = !![(129 / 80 : ℂ), 31 / 40; 31 / 40, 9 / 20] := by
      have hlinear :
          cfc (fun x : ℝ => (31 / 80 / Real.log 2) * x) b01A =
            (31 / 80 / Real.log 2) • b01A := by
        convert
          (cfc_const_mul_id (R := ℝ) (31 / 80 / Real.log 2) b01A b01A_hermitian) using 1
      have hconst : cfc (fun _ : ℝ => 129 / 80) b01A =
          algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) (129 / 80) := by
        exact cfc_const (129 / 80) b01A b01A_hermitian
      rw [show (fun x : ℝ => (31 / 80) * (x / Real.log 2) + 129 / 80) =
          (fun x : ℝ => (31 / 80 / Real.log 2) * x + 129 / 80) by
            funext x
            ring,
        cfc_add (a := b01A) (fun x : ℝ => (31 / 80 / Real.log 2) * x)
          (fun _ : ℝ => 129 / 80) (by fun_prop) (by fun_prop),
        hlinear, hconst]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [b01A, b01A0, Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def]
      all_goals rw [← hlog_eq]
      all_goals field_simp [hlog, hlogC]
      all_goals norm_num

private lemma b01_cfc_H :
    cfc Real.exp b01H = !![(18 / 5 : ℂ), 31 / 5; 31 / 5, 129 / 10] := by
  have hlog : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hlogC : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
  have hlog_eq : (Real.log 2 : ℂ) = Complex.log 2 := by
    convert Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2) using 1
    all_goals norm_num
  calc
    cfc Real.exp b01H =
        cfc (fun x : ℝ => (31 / 10) * (x / Real.log 2) + 18 / 5) b01H := by
      apply cfc_congr
      intro x hx
      rcases b01H_spectrum hx with h | h
      · subst x
        rw [b01_exp_four_log_two]
        field_simp
        norm_num
      · subst x
        rw [b01_exp_neg_log_two]
        field_simp
        norm_num
    _ = !![(18 / 5 : ℂ), 31 / 5; 31 / 5, 129 / 10] := by
      have hlinear :
          cfc (fun x : ℝ => (31 / 10 / Real.log 2) * x) b01H =
            (31 / 10 / Real.log 2) • b01H := by
        convert
          (cfc_const_mul_id (R := ℝ) (31 / 10 / Real.log 2) b01H b01H_hermitian) using 1
      have hconst : cfc (fun _ : ℝ => 18 / 5) b01H =
          algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) (18 / 5) := by
        exact cfc_const (18 / 5) b01H b01H_hermitian
      rw [show (fun x : ℝ => (31 / 10) * (x / Real.log 2) + 18 / 5) =
          (fun x : ℝ => (31 / 10 / Real.log 2) * x + 18 / 5) by
            funext x
            ring,
        cfc_add (a := b01H) (fun x : ℝ => (31 / 10 / Real.log 2) * x)
          (fun _ : ℝ => 18 / 5) (by fun_prop) (by fun_prop),
        hlinear, hconst]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [b01H, b01H0, Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def]
      all_goals rw [← hlog_eq]
      all_goals field_simp [hlog, hlogC]
      all_goals norm_num

private lemma b01_cfc_M :
    cfc Real.exp b01M = !![(17 / 8 : ℂ), 15 / 8; 15 / 8, 17 / 8] := by
  have hlog : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hlogC : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
  have hlog_eq : (Real.log 2 : ℂ) = Complex.log 2 := by
    convert Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2) using 1
    all_goals norm_num
  calc
    cfc Real.exp b01M =
        cfc (fun x : ℝ => (15 / 16) * (x / Real.log 2) + 17 / 8) b01M := by
      apply cfc_congr
      intro x hx
      rcases b01M_spectrum hx with h | h
      · subst x
        rw [b01_exp_two_log_two]
        field_simp
        norm_num
      · subst x
        rw [b01_exp_neg_two_log_two]
        field_simp
        norm_num
    _ = !![(17 / 8 : ℂ), 15 / 8; 15 / 8, 17 / 8] := by
      have hlinear :
          cfc (fun x : ℝ => (15 / 16 / Real.log 2) * x) b01M =
            (15 / 16 / Real.log 2) • b01M := by
        convert
          (cfc_const_mul_id (R := ℝ) (15 / 16 / Real.log 2) b01M b01M_hermitian) using 1
      have hconst : cfc (fun _ : ℝ => 17 / 8) b01M =
          algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) (17 / 8) := by
        exact cfc_const (17 / 8) b01M b01M_hermitian
      rw [show (fun x : ℝ => (15 / 16) * (x / Real.log 2) + 17 / 8) =
          (fun x : ℝ => (15 / 16 / Real.log 2) * x + 17 / 8) by
            funext x
            ring,
        cfc_add (a := b01M) (fun x : ℝ => (15 / 16 / Real.log 2) * x)
          (fun _ : ℝ => 17 / 8) (by fun_prop) (by fun_prop),
        hlinear, hconst]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [b01M, b01M0, Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def]
      all_goals rw [← hlog_eq]
      all_goals field_simp [hlog, hlogC]
      all_goals norm_num

private lemma b01_midpoint :
    (1 / 2 : ℝ) • b01A + (1 - 1 / 2 : ℝ) • b01H = b01M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [b01A, b01H, b01M, b01A0, b01H0, b01M0]
  all_goals ring

/-- **Book §8.4.5, bullet 2 (B-01).** "The exponential function is not
operator convex on the real line."  Take
`A = log(2) • [[0,2],[2,-3]]` and `H = log(2) • [[0,2],[2,3]]`.
Their eigenvalues, and those of their midpoint, are integer multiples of
`log 2`, so all three matrix exponentials reduce exactly to rational matrices.
The alleged midpoint-convexity defect has quadratic form `-13/20` at the
vector `(4,-1)`; no numerical approximation is used. -/
theorem not_operatorConvexOn_exp :
    ¬ OperatorConvexOn (Fin 2) Real.exp Set.univ := by
  intro hconv
  have hineq := hconv b01A b01H b01A_hermitian b01H_hermitian
    (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _)
    (1 / 2) (by constructor <;> norm_num)
  rw [b01_midpoint, b01_cfc_A, b01_cfc_H, b01_cfc_M] at hineq
  have hpsd := Matrix.le_iff.mp hineq
  have hq := hpsd.dotProduct_mulVec_nonneg ![(4 : ℂ), -1]
  have hstarvec : star ![(4 : ℂ), -1] = ![(4 : ℂ), -1] := by
    ext i
    fin_cases i
    · change star (4 : ℂ) = 4
      exact Complex.conj_ofReal 4
    · change star (-1 : ℂ) = -1
      rw [star_neg, star_one]
  have hval : star ![(4 : ℂ), -1] ⬝ᵥ
      (((1 / 2 : ℝ) • !![(129 / 80 : ℂ), 31 / 40; 31 / 40, 9 / 20] +
        (1 - 1 / 2 : ℝ) • !![(18 / 5 : ℂ), 31 / 5; 31 / 5, 129 / 10] -
        !![(17 / 8 : ℂ), 15 / 8; 15 / 8, 17 / 8]) *ᵥ
        ![(4 : ℂ), -1]) = (-13 / 20 : ℂ) := by
    rw [hstarvec]
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply]
  rw [hval] at hq
  have hre := (Complex.le_def.mp hq).1
  norm_num at hre

end OperatorConvexDef

/-! ## Schur complements (§8.4.6, Fact 8.4.7) -/

section SchurComplement

/-- **Book Fact (Schur Complements, 8.4.7)**  "Suppose that
`T` is a positive-definite matrix.  Then `0 ≼ [[T, B], [Bᴴ, M]]` if and
only if `Bᴴ T⁻¹ B ≼ M`."  Correspondence: Mathlib's
`Matrix.PosSemidef.fromBlocks₁₁` (block Gaussian elimination, the book's
proof). -/
theorem schur_complement_posSemidef_iff {m : Type*} [Fintype m]
    [DecidableEq m] (hT : T.PosDef) (B : Matrix n m ℂ) (M : Matrix m m ℂ) :
    (Matrix.fromBlocks T B Bᴴ M).PosSemidef ↔ Bᴴ * T⁻¹ * B ≤ M := by
  haveI := hT.isUnit.invertible
  rw [Matrix.PosDef.fromBlocks₁₁ B M hT, ← Matrix.le_iff]

/-- **Book equation (8.4.6)**  "`0 ≼ [[T, I], [I, T⁻¹]]` whenever `T`
is positive definite." -/
lemma posSemidef_fromBlocks_one_inv (hT : T.PosDef) :
    (Matrix.fromBlocks T (1 : Matrix n n ℂ) (1 : Matrix n n ℂ)
      T⁻¹).PosSemidef := by
  have h1 : (Matrix.fromBlocks T (1 : Matrix n n ℂ) (1 : Matrix n n ℂ) T⁻¹) =
      Matrix.fromBlocks T (1 : Matrix n n ℂ) (1 : Matrix n n ℂ)ᴴ T⁻¹ := by
    rw [Matrix.conjTranspose_one]
  rw [h1, schur_complement_posSemidef_iff hT, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]

end SchurComplement

/-! ## The inverse is operator convex (§8.4.6, Proposition
8.4.6) -/

section InverseConvex

/-- Lean implementation helper: a convex combination of pd matrices is pd
(the book's "the top-left block of the latter matrix is positive
definite"). -/
lemma posDef_convex_combo (hA : A.PosDef) (hH : H.PosDef) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : (τ • A + (1 - τ) • H).PosDef := by
  rcases eq_or_lt_of_le hτ.1 with h0 | h0
  · rw [← h0]
    simpa using hH
  · exact (hA.smul h0).add_posSemidef
      (hH.posSemidef.smul (by linarith [hτ.2]))

/-- **Book Proposition (Inverse is Operator Convex, 8.4.6),
displayed form**  "for positive-definite matrices `A` and `H`,
`(τA + τ̄H + uI)⁻¹ ≼ τ·(A + uI)⁻¹ + τ̄·(H + uI)⁻¹` for `τ ∈ [0,1]`"
(`u ≥ 0`) — the book's Schur-complement proof. -/
theorem inv_shift_operator_convex {u : ℝ} (hu : 0 ≤ u) (hA : A.PosDef)
    (hH : H.PosDef) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (τ • A + (1 - τ) • H + u • 1)⁻¹ ≤
      τ • (A + u • 1)⁻¹ + (1 - τ) • (H + u • 1)⁻¹ := by
  set Au := A + u • (1 : Matrix n n ℂ) with hAu
  set Hu := H + u • (1 : Matrix n n ℂ) with hHu
  have hAupd : Au.PosDef := posDef_add_smul_one hA hu
  have hHupd : Hu.PosDef := posDef_add_smul_one hH hu
  have hcomb : (τ • Au + (1 - τ) • Hu).PosDef :=
    posDef_convex_combo hAupd hHupd hτ
  have hKey : τ • Au + (1 - τ) • Hu = τ • A + (1 - τ) • H + u • 1 := by
    rw [hAu, hHu]
    module
  -- the convex combination of the two (8.4.6) block matrices
  have h1 : (Matrix.fromBlocks (τ • Au + (1 - τ) • Hu)
      (1 : Matrix n n ℂ) (1 : Matrix n n ℂ)
      (τ • Au⁻¹ + (1 - τ) • Hu⁻¹)).PosSemidef := by
    have h2 := (posSemidef_fromBlocks_one_inv hAupd).smul hτ.1
    have h3 := (posSemidef_fromBlocks_one_inv hHupd).smul
      (show (0 : ℝ) ≤ 1 - τ by linarith [hτ.2])
    have h4 := h2.add h3
    rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_add] at h4
    have h5 : τ • (1 : Matrix n n ℂ) + (1 - τ) • 1 = 1 := by module
    rwa [h5] at h4
  -- Schur back, using that the top-left block is pd
  have h6 : (1 : Matrix n n ℂ)ᴴ * (τ • Au + (1 - τ) • Hu)⁻¹ * 1 ≤
      τ • Au⁻¹ + (1 - τ) • Hu⁻¹ := by
    refine (schur_complement_posSemidef_iff hcomb 1 _).mp ?_
    have h7 : (Matrix.fromBlocks (τ • Au + (1 - τ) • Hu)
        (1 : Matrix n n ℂ) ((1 : Matrix n n ℂ))ᴴ
        (τ • Au⁻¹ + (1 - τ) • Hu⁻¹)) =
        (Matrix.fromBlocks (τ • Au + (1 - τ) • Hu)
        (1 : Matrix n n ℂ) (1 : Matrix n n ℂ)
        (τ • Au⁻¹ + (1 - τ) • Hu⁻¹)) := by
      rw [Matrix.conjTranspose_one]
    rw [h7]
    exact h1
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hKey] at h6
  exact h6

/-- **Book Proposition 8.4.6, abstract form**  "For each `u ≥ 0`,
the function `a ↦ (a + u)⁻¹` is operator convex on the positive real
line." -/
theorem operatorConvexOn_inv_shift (n : Type*) [Fintype n] [DecidableEq n]
    {u : ℝ} (hu : 0 ≤ u) :
    OperatorConvexOn n (fun a => (a + u)⁻¹) (Set.Ioi 0) := by
  intro A H hA hH hAI hHI τ hτ
  have hApd : A.PosDef :=
    posDef_iff_exists_eigenvalues_pos.mpr ⟨hA, fun i => hAI i⟩
  have hHpd : H.PosDef :=
    posDef_iff_exists_eigenvalues_pos.mpr ⟨hH, fun i => hHI i⟩
  have hcomb : (τ • A + (1 - τ) • H).PosDef := posDef_convex_combo hApd hHpd hτ
  rw [← inv_shift_eq_cfc hApd hu, ← inv_shift_eq_cfc hHpd hu,
    ← inv_shift_eq_cfc hcomb hu]
  exact inv_shift_operator_convex hu hApd hHpd hτ

end InverseConvex

/-! ## The logarithm is operator concave (§8.4.7–8, Proposition
8.4.8) -/

section LogConcave

/-- **Book Proposition (Logarithm is Operator Concave, 8.4.8),
displayed form**  "for positive-definite matrices `A` and `H`,
`τ·log A + τ̄·log H ≼ log(τA + τ̄H)` for `τ ∈ [0,1]`" — by the integral
representation, the operator convexity of the inverse, and preservation of
the semidefinite order under integration. -/
theorem log_operator_concave (hA : A.PosDef) (hH : H.PosDef) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    τ • CFC.log A + (1 - τ) • CFC.log H ≤
      CFC.log (τ • A + (1 - τ) • H) := by
  have hKpd : (τ • A + (1 - τ) • H).PosDef := posDef_convex_combo hA hH hτ
  have hIA : IntegrableOn
      (fun u : ℝ => τ • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹))
      (Set.Ioi 0) := (integrableOn_matrix_log_kernel hA).smul τ
  have hIH : IntegrableOn
      (fun u : ℝ =>
        (1 - τ) • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (H + u • 1)⁻¹))
      (Set.Ioi 0) := (integrableOn_matrix_log_kernel hH).smul (1 - τ)
  rw [Matrix.le_iff]
  have h1 : CFC.log (τ • A + (1 - τ) • H) -
      (τ • CFC.log A + (1 - τ) • CFC.log H) =
      ∫ u in Set.Ioi (0 : ℝ),
        (((1 + u)⁻¹ • (1 : Matrix n n ℂ) -
            (τ • A + (1 - τ) • H + u • 1)⁻¹) -
          (τ • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹) +
            (1 - τ) • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (H + u • 1)⁻¹))) := by
    have e1 : (∫ u in Set.Ioi (0 : ℝ),
        (((1 + u)⁻¹ • (1 : Matrix n n ℂ) -
            (τ • A + (1 - τ) • H + u • 1)⁻¹) -
          (τ • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹) +
            (1 - τ) • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (H + u • 1)⁻¹)))) =
        (∫ u in Set.Ioi (0 : ℝ),
          ((1 + u)⁻¹ • (1 : Matrix n n ℂ) -
            (τ • A + (1 - τ) • H + u • 1)⁻¹)) -
        ∫ u in Set.Ioi (0 : ℝ),
          (τ • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹) +
            (1 - τ) • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (H + u • 1)⁻¹)) :=
      integral_sub (integrableOn_matrix_log_kernel hKpd) (hIA.add hIH)
    have e2 : (∫ u in Set.Ioi (0 : ℝ),
        (τ • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹) +
          (1 - τ) • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (H + u • 1)⁻¹))) =
        (∫ u in Set.Ioi (0 : ℝ),
          τ • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹)) +
        ∫ u in Set.Ioi (0 : ℝ),
          (1 - τ) • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (H + u • 1)⁻¹) :=
      integral_add hIA hIH
    have e3 : (∫ u in Set.Ioi (0 : ℝ),
        τ • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹)) =
        τ • ∫ u in Set.Ioi (0 : ℝ),
          ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹) :=
      integral_smul _ _
    have e4 : (∫ u in Set.Ioi (0 : ℝ),
        (1 - τ) • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (H + u • 1)⁻¹)) =
        (1 - τ) • ∫ u in Set.Ioi (0 : ℝ),
          ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (H + u • 1)⁻¹) :=
      integral_smul _ _
    rw [e1, e2, e3, e4, ← matrix_log_eq_integral hA,
      ← matrix_log_eq_integral hH, ← matrix_log_eq_integral hKpd]
  rw [h1]
  refine posSemidef_setIntegral measurableSet_Ioi
    ((integrableOn_matrix_log_kernel hKpd).sub (hIA.add hIH))
    fun u hu => ?_
  have h2 : ((1 + u)⁻¹ • (1 : Matrix n n ℂ) -
      (τ • A + (1 - τ) • H + u • 1)⁻¹) -
      (τ • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (A + u • 1)⁻¹) +
        (1 - τ) • ((1 + u)⁻¹ • (1 : Matrix n n ℂ) - (H + u • 1)⁻¹)) =
      (τ • (A + u • 1)⁻¹ + (1 - τ) • (H + u • 1)⁻¹) -
        (τ • A + (1 - τ) • H + u • 1)⁻¹ := by
    module
  rw [h2, ← Matrix.le_iff]
  exact inv_shift_operator_convex (le_of_lt hu) hA hH hτ

/-- **Book Proposition 8.4.8, abstract form**  "The logarithm is
operator concave on the positive real line." -/
theorem operatorConcaveOn_log (n : Type*) [Fintype n] [DecidableEq n] :
    OperatorConcaveOn n Real.log (Set.Ioi 0) := by
  intro A H hA hH hAI hHI τ hτ
  have hApd : A.PosDef :=
    posDef_iff_exists_eigenvalues_pos.mpr ⟨hA, fun i => hAI i⟩
  have hHpd : H.PosDef :=
    posDef_iff_exists_eigenvalues_pos.mpr ⟨hH, fun i => hHI i⟩
  have hcomb : (τ • A + (1 - τ) • H).PosDef := posDef_convex_combo hApd hHpd hτ
  have hkey : ∀ (M : Matrix n n ℂ) (hM : M.PosDef),
      cfc (fun t : ℝ => -Real.log t) M = -CFC.log M := by
    intro M hM
    have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM.1
    exact cfc_neg Real.log M
  rw [hkey _ hcomb, hkey A hApd, hkey H hHpd, smul_neg, smul_neg, ← neg_add]
  exact neg_le_neg (log_operator_concave hApd hHpd hτ)

end LogConcave

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# §8.5: The Operator Jensen Inequality

* **Definition (Matrix Convex Combination, 8.5.1)** 
  rendered by the hypothesis pattern `K₁ᴴK₁ + K₂ᴴK₂ = 1` together with the
  expression `K₁ᴴA₁K₁ + K₂ᴴA₂K₂`.
* **§8.5.1 bullet list**  `matrix_convex_combo_scalar` (scalar convex
  combinations are matrix convex combinations, via `K₁ = √τ·I`),
  `matrix_convex_combo_one` (preservation of the identity),
  `matrix_convex_combo_posSemidef` (preservation of positivity),
  `matrix_convex_combo_eigenvalues_mem` (eigenvalues stay in the
  interval `I`; the interval structure enters as `Set.OrdConnected`).
* **Theorem (Operator Jensen Inequality, 8.5.2)** 
  `operator_jensen`. The operator-convexity hypothesis is consumed at the doubled index type
  `n ⊕ n`.
* Recovered implicit prerequisites: the unitary completion of an isometric
  column pair (`exists_unitary_completion`, the book's "we can choose `L₁`
  and `L₂` to complete the unitary matrix `Q`"), the block-diagonal
  functional calculus (`cfc_fromBlocks_diag`, the book's "we can apply a
  standard matrix function to a block-diagonal matrix by applying the
  function to each block"), unitary conjugation of the functional calculus
  (`cfc_conj_unitary`, the book's "a standard matrix function commutes with
  unitary conjugation"), the `U`-averaging identity
  (`half_avg_conj_diag`, display (8.5.6)), the (1,1)
  block computation (`conj_block_toBlocks₁₁`, display
  (8.5.5)), monotonicity of the `[·]₁₁` operation
  (`toBlocks₁₁_loewner_mono`), and spectral bookkeeping for unitary
  conjugations and block-diagonal matrices.
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A H M : Matrix n n ℂ}

/-! ## Spectral bookkeeping -/

section SpectrumTransport

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Lean implementation helper: eigenvalue membership is spectrum
containment. -/
lemma eigenvalues_mem_of_spectrum_subset {M : Matrix m m ℂ}
    (hM : M.IsHermitian) {I : Set ℝ} (h : spectrum ℝ M ⊆ I) :
    ∀ i, hM.eigenvalues i ∈ I := fun i => h (by
  rw [hM.spectrum_real_eq_range_eigenvalues]
  exact Set.mem_range_self i)

/-- Lean implementation helper: spectrum containment from eigenvalue
membership. -/
lemma spectrum_subset_of_eigenvalues_mem {M : Matrix m m ℂ}
    (hM : M.IsHermitian) {I : Set ℝ} (h : ∀ i, hM.eigenvalues i ∈ I) :
    spectrum ℝ M ⊆ I := by
  rw [hM.spectrum_real_eq_range_eigenvalues]
  exact Set.range_subset_iff.mpr h

/-- Lean implementation helper: the spectrum is invariant under unitary
conjugation (the eigenvalue bookkeeping behind (8.5.5)).
-/
lemma spectrum_conj_unitary {Q M : Matrix m m ℂ}
    (h1 : Qᴴ * Q = 1) (h2 : Q * Qᴴ = 1) :
    spectrum ℝ (Qᴴ * M * Q) = spectrum ℝ M := by
  have hQu : IsUnit Q := ⟨⟨Q, Qᴴ, h2, h1⟩, rfl⟩
  have hQdu : IsUnit Qᴴ := ⟨⟨Qᴴ, Q, h1, h2⟩, rfl⟩
  have hiff : ∀ X : Matrix m m ℂ, IsUnit (Qᴴ * X * Q) ↔ IsUnit X := by
    intro X
    constructor
    · intro h
      have h3 : Q * (Qᴴ * X * Q) * Qᴴ = X := by
        calc Q * (Qᴴ * X * Q) * Qᴴ = (Q * Qᴴ) * X * (Q * Qᴴ) := by
              noncomm_ring
          _ = X := by rw [h2, Matrix.one_mul, Matrix.mul_one]
      rw [← h3]
      exact (hQu.mul h).mul hQdu
    · intro h
      exact (hQdu.mul h).mul hQu
  have key : ∀ z : ℝ, (algebraMap ℝ (Matrix m m ℂ) z) - Qᴴ * M * Q =
      Qᴴ * ((algebraMap ℝ (Matrix m m ℂ) z) - M) * Q := by
    intro z
    have h4 : Qᴴ * (algebraMap ℝ (Matrix m m ℂ) z) * Q =
        algebraMap ℝ (Matrix m m ℂ) z := by
      rw [Algebra.algebraMap_eq_smul_one]
      calc Qᴴ * (z • (1 : Matrix m m ℂ)) * Q = z • (Qᴴ * 1 * Q) := by
            rw [mul_smul_comm, smul_mul_assoc]
        _ = z • (1 : Matrix m m ℂ) := by rw [Matrix.mul_one, h1]
    rw [Matrix.mul_sub, Matrix.sub_mul, h4]
  ext z
  rw [spectrum.mem_iff, spectrum.mem_iff, key z, not_iff_not]
  exact hiff _

/-- Lean implementation helper: the spectrum of a block-diagonal matrix is
contained in the union of the block spectra (the book's "the matrix `A`
lies in the domain of `f` because its eigenvalues fall in the interval
`I`"). -/
lemma spectrum_fromBlocks_diag_subset {M₁ M₂ : Matrix n n ℂ} :
    spectrum ℝ (Matrix.fromBlocks M₁ 0 0 M₂) ⊆
      spectrum ℝ M₁ ∪ spectrum ℝ M₂ := by
  intro z hz
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [spectrum.notMem_iff] at h1 h2
  refine (spectrum.mem_iff.mp hz) ?_
  have key : (algebraMap ℝ (Matrix (n ⊕ n) (n ⊕ n) ℂ) z) -
      Matrix.fromBlocks M₁ 0 0 M₂ =
      Matrix.fromBlocks ((algebraMap ℝ (Matrix n n ℂ) z) - M₁) 0 0
        ((algebraMap ℝ (Matrix n n ℂ) z) - M₂) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      ← Matrix.fromBlocks_one (l := n) (m := n), Matrix.fromBlocks_smul]
    ext (i | i) (j | j) <;>
      simp [Matrix.fromBlocks, Matrix.sub_apply]
  rw [key]
  obtain ⟨u₁, hu₁⟩ := h1
  obtain ⟨u₂, hu₂⟩ := h2
  refine ⟨⟨Matrix.fromBlocks ↑u₁ 0 0 ↑u₂,
    Matrix.fromBlocks ↑u₁⁻¹ 0 0 ↑u₂⁻¹, ?_, ?_⟩, by rw [← hu₁, ← hu₂]⟩
  · rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  · rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]

end SpectrumTransport

/-! ## Eigenvalue bounds from Loewner comparisons with `c·I` -/

section EigenvalueBounds

/-- Lean implementation helper: `c·I ≼ M` from a pointwise eigenvalue
bound. -/
lemma smul_one_le_of_forall_le {c : ℝ} (hM : M.IsHermitian)
    (hc : ∀ i, c ≤ hM.eigenvalues i) : c • (1 : Matrix n n ℂ) ≤ M := by
  have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  have h1 : cfc (fun _ : ℝ => c) M ≤ cfc (id : ℝ → ℝ) M :=
    transfer_rule hM (I := {x : ℝ | c ≤ x}) (fun i => hc i) fun x hx => hx
  rwa [cfc_const c M, cfc_id ℝ M, Algebra.algebraMap_eq_smul_one] at h1

/-- Lean implementation helper: `M ≼ c·I` from a pointwise eigenvalue
bound. -/
lemma le_smul_one_of_forall_le {c : ℝ} (hM : M.IsHermitian)
    (hc : ∀ i, hM.eigenvalues i ≤ c) : M ≤ c • (1 : Matrix n n ℂ) := by
  have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  have h1 : cfc (id : ℝ → ℝ) M ≤ cfc (fun _ : ℝ => c) M :=
    transfer_rule hM (I := {x : ℝ | x ≤ c}) (fun i => hc i) fun x hx => hx
  rwa [cfc_const c M, cfc_id ℝ M, Algebra.algebraMap_eq_smul_one] at h1

/-- Lean implementation helper: the Rayleigh value of `c·I` at a unit
vector is `c`. -/
private lemma rayleigh_smul_one {c : ℝ} {u : n → ℂ} (hu : l2norm u = 1) :
    rayleigh (c • (1 : Matrix n n ℂ)) u = c := by
  rw [rayleigh, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    dotProduct_star_self_eq, hu]
  norm_num

/-- Lean implementation helper: a lower Loewner bound `c·I ≼ M` bounds all
eigenvalues below. -/
lemma le_eigenvalues_of_smul_one_le {c : ℝ} (hM : M.IsHermitian)
    (h : c • (1 : Matrix n n ℂ) ≤ M) : ∀ i, c ≤ hM.eigenvalues i := by
  intro i
  have h1 := rayleigh_mono_of_loewner_le h (⇑(hM.eigenvectorBasis i))
  rw [rayleigh_eigenvectorBasis hM i,
    rayleigh_smul_one (l2norm_eigenvectorBasis hM i)] at h1
  exact h1

/-- Lean implementation helper: an upper Loewner bound `M ≼ c·I` bounds all
eigenvalues above. -/
lemma eigenvalues_le_of_le_smul_one {c : ℝ} (hM : M.IsHermitian)
    (h : M ≤ c • (1 : Matrix n n ℂ)) : ∀ i, hM.eigenvalues i ≤ c := by
  intro i
  have h1 := rayleigh_mono_of_loewner_le h (⇑(hM.eigenvectorBasis i))
  rw [rayleigh_eigenvectorBasis hM i,
    rayleigh_smul_one (l2norm_eigenvectorBasis hM i)] at h1
  exact h1

end EigenvalueBounds

/-! ## Block-matrix plumbing -/

section BlockPlumbing

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- Lean implementation helper: a block-diagonal matrix with Hermitian
blocks is Hermitian. -/
lemma isHermitian_fromBlocks_diag {A₁ : Matrix n n ℂ} {A₂ : Matrix l l ℂ}
    (h1 : A₁.IsHermitian) (h2 : A₂.IsHermitian) :
    (Matrix.fromBlocks A₁ 0 0 A₂).IsHermitian := by
  show _ᴴ = _
  rw [Matrix.fromBlocks_conjTranspose, h1.eq, h2.eq,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_zero]

/-- Lean implementation helper: the (1,1) block of a Hermitian matrix is
Hermitian. -/
lemma toBlocks₁₁_isHermitian {W : Matrix (n ⊕ l) (n ⊕ l) ℂ}
    (hW : W.IsHermitian) : (W.toBlocks₁₁).IsHermitian := by
  ext i j
  have h1 : Wᴴ (Sum.inl i) (Sum.inl j) = W (Sum.inl i) (Sum.inl j) := by
    rw [hW.eq]
  simpa [Matrix.toBlocks₁₁, Matrix.conjTranspose_apply] using h1

/-- Lean implementation helper: the (2,2) block of a Hermitian matrix is
Hermitian. -/
lemma toBlocks₂₂_isHermitian {W : Matrix (n ⊕ l) (n ⊕ l) ℂ}
    (hW : W.IsHermitian) : (W.toBlocks₂₂).IsHermitian := by
  ext i j
  have h1 : Wᴴ (Sum.inr i) (Sum.inr j) = W (Sum.inr i) (Sum.inr j) := by
    rw [hW.eq]
  simpa [Matrix.toBlocks₂₂, Matrix.conjTranspose_apply] using h1

/-- Lean implementation helper: the (1,1) block of a psd matrix is psd
(quadratic form with vectors supported on the first summand). -/
lemma toBlocks₁₁_posSemidef {W : Matrix (n ⊕ l) (n ⊕ l) ℂ}
    (hW : W.PosSemidef) : (W.toBlocks₁₁).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (toBlocks₁₁_isHermitian hW.1) fun x => ?_
  have h1 := hW.dotProduct_mulVec_nonneg (Sum.elim x 0)
  have h2 : star (Sum.elim x 0) ⬝ᵥ (W *ᵥ Sum.elim x 0) =
      star x ⬝ᵥ (W.toBlocks₁₁ *ᵥ x) := by
    simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
      Matrix.toBlocks₁₁]
  rwa [h2] at h1

/-- **Book Theorem 8.5.2 (proof step).**

**Implicit fact (proof of 8.5.2)**  passing to the
(1,1) block preserves the semidefinite order. -/
lemma toBlocks₁₁_loewner_mono {X Y : Matrix (n ⊕ l) (n ⊕ l) ℂ}
    (h : X ≤ Y) : X.toBlocks₁₁ ≤ Y.toBlocks₁₁ := by
  rw [Matrix.le_iff] at h ⊢
  have h1 := toBlocks₁₁_posSemidef h
  have h2 : (Y - X).toBlocks₁₁ = Y.toBlocks₁₁ - X.toBlocks₁₁ := by
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.sub_apply]
  rwa [h2] at h1

/-- **Book Theorem 8.5.2 (proof sign matrix).**

The book's sign matrix `U = [[I, 0], [0, −I]]` from the proof of
8.5.2. -/
noncomputable def blockU (n l : Type*) [Fintype n] [Fintype l]
    [DecidableEq n] [DecidableEq l] : Matrix (n ⊕ l) (n ⊕ l) ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Lean implementation helper. -/
lemma blockU_conjTranspose : (blockU n l)ᴴ = blockU n l := by
  rw [blockU, Matrix.fromBlocks_conjTranspose]
  congr 1 <;> simp

/-- Lean implementation helper. -/
lemma blockU_mul_self : blockU n l * blockU n l = 1 := by
  rw [blockU, Matrix.fromBlocks_multiply]
  simp

/-- Lean implementation helper. -/
lemma blockU_conj_mul : (blockU n l)ᴴ * blockU n l = 1 := by
  rw [blockU_conjTranspose, blockU_mul_self]

/-- Lean implementation helper. -/
lemma blockU_mul_conj : blockU n l * (blockU n l)ᴴ = 1 := by
  rw [blockU_conjTranspose, blockU_mul_self]

/-- **Book equation (8.5.6)**, generic-block form: the
two-point unitary average kills the off-diagonal blocks. -/
lemma half_avg_conj_diag' (T : Matrix n n ℂ) (B : Matrix n l ℂ)
    (C : Matrix l n ℂ) (D : Matrix l l ℂ) :
    (1/2 : ℝ) • Matrix.fromBlocks T B C D +
      (1/2 : ℝ) • ((blockU n l)ᴴ * Matrix.fromBlocks T B C D *
        blockU n l) = Matrix.fromBlocks T 0 0 D := by
  have hconj : (blockU n l)ᴴ * Matrix.fromBlocks T B C D * blockU n l =
      Matrix.fromBlocks T (-B) (-C) D := by
    rw [blockU_conjTranspose, blockU, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp
  rw [hconj, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_add]
  have e1 : (1/2 : ℝ) • T + (1/2 : ℝ) • T = T := by module
  have e2 : (1/2 : ℝ) • B + (1/2 : ℝ) • -B = (0 : Matrix n l ℂ) := by
    module
  have e3 : (1/2 : ℝ) • C + (1/2 : ℝ) • -C = (0 : Matrix l n ℂ) := by
    module
  have e4 : (1/2 : ℝ) • D + (1/2 : ℝ) • D = D := by module
  rw [e1, e2, e3, e4]

/-- **Book equation (8.5.6)**  "for any block matrix,
`½·W + ½·Uᴴ W U = [[T, 0], [0, M]]`" — the two-point unitary average that
kills the off-diagonal blocks. -/
lemma half_avg_conj_diag (W : Matrix (n ⊕ l) (n ⊕ l) ℂ) :
    (1/2 : ℝ) • W + (1/2 : ℝ) • ((blockU n l)ᴴ * W * blockU n l) =
      Matrix.fromBlocks (W.toBlocks₁₁) 0 0 (W.toBlocks₂₂) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks W]
  exact half_avg_conj_diag' _ _ _ _

end BlockPlumbing

/-! ## Functional-calculus plumbing -/

section CfcPlumbing

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Book Theorem 8.5.2 (proof step).**

**Implicit fact (proof of 8.5.2)**  "a standard matrix
function commutes with unitary conjugation":
`f(Qᴴ M Q) = Qᴴ f(M) Q`. -/
lemma cfc_conj_unitary {Q M : Matrix m m ℂ} (hM : M.IsHermitian)
    (h1 : Qᴴ * Q = 1) (_h2 : Q * Qᴴ = 1) (f : ℝ → ℝ) :
    cfc f (Qᴴ * M * Q) = Qᴴ * cfc f M * Q := by
  have hMher : (Qᴴ * M * Q).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul Q hM
  set V := (hM.eigenvectorUnitary : Matrix m m ℂ) with hV
  have hVV : V * Vᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.2
    simpa [star_eq_conjTranspose] using h
  have hQV : Qᴴ * V ∈ Matrix.unitaryGroup m ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Qᴴ * V * (Vᴴ * Q) = Qᴴ * (V * Vᴴ) * Q := by noncomm_ring
      _ = 1 := by rw [hVV, Matrix.mul_one, h1]
  have hdecomp : Qᴴ * M * Q = (Qᴴ * V) *
      Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) * (Qᴴ * V)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Qᴴ * M * Q
        = Qᴴ * (V * Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) * Vᴴ) *
          Q := by rw [← spectral_decomposition hM]
      _ = Qᴴ * V * Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) *
          (Vᴴ * Q) := by noncomm_ring
  rw [cfc_unitary_diagonal hMher hQV hdecomp f, cfc_eq_book_formula hM f,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  noncomm_ring

/-- **Book Theorem 8.5.2 (proof step).**

**Implicit fact (proof of 8.5.2)**  "we can apply a
standard matrix function to a block-diagonal matrix by applying the
function to each block." -/
lemma cfc_fromBlocks_diag {A₁ A₂ : Matrix n n ℂ} (hA₁ : A₁.IsHermitian)
    (hA₂ : A₂.IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.fromBlocks A₁ 0 0 A₂) =
      Matrix.fromBlocks (cfc f A₁) 0 0 (cfc f A₂) := by
  set V₁ := (hA₁.eigenvectorUnitary : Matrix n n ℂ) with hV₁
  set V₂ := (hA₂.eigenvectorUnitary : Matrix n n ℂ) with hV₂
  have hV₁m := Matrix.mem_unitaryGroup_iff.mp hA₁.eigenvectorUnitary.2
  have hV₂m := Matrix.mem_unitaryGroup_iff.mp hA₂.eigenvectorUnitary.2
  have hV₁V : V₁ * V₁ᴴ = 1 := by simpa [star_eq_conjTranspose] using hV₁m
  have hV₂V : V₂ * V₂ᴴ = 1 := by simpa [star_eq_conjTranspose] using hV₂m
  set U : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks V₁ 0 0 V₂ with hUdef
  have hU : U ∈ Matrix.unitaryGroup (n ⊕ n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, hUdef,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp [hV₁V, hV₂V]
  have helim : (RCLike.ofReal ∘ Sum.elim hA₁.eigenvalues hA₂.eigenvalues :
      n ⊕ n → ℂ) = Sum.elim (RCLike.ofReal ∘ hA₁.eigenvalues)
        (RCLike.ofReal ∘ hA₂.eigenvalues) := by
    funext p
    cases p <;> rfl
  have hd : Matrix.fromBlocks A₁ 0 0 A₂ = U *
      Matrix.diagonal (RCLike.ofReal ∘
        Sum.elim hA₁.eigenvalues hA₂.eigenvalues) * Uᴴ := by
    rw [helim, ← Matrix.fromBlocks_diagonal, hUdef,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.conjTranspose_zero]
    rw [← spectral_decomposition hA₁, ← spectral_decomposition hA₂]
  have hbig : (Matrix.fromBlocks A₁ 0 0 A₂).IsHermitian :=
    isHermitian_fromBlocks_diag hA₁ hA₂
  rw [cfc_unitary_diagonal hbig hU hd f]
  have helim' : (RCLike.ofReal ∘ f ∘
      Sum.elim hA₁.eigenvalues hA₂.eigenvalues : n ⊕ n → ℂ) =
      Sum.elim (RCLike.ofReal ∘ f ∘ hA₁.eigenvalues)
        (RCLike.ofReal ∘ f ∘ hA₂.eigenvalues) := by
    funext p
    cases p <;> rfl
  rw [helim', ← Matrix.fromBlocks_diagonal, hUdef,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, cfc_eq_book_formula hA₁ f,
    cfc_eq_book_formula hA₂ f]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.conjTranspose_zero]
  congr 1

end CfcPlumbing

/-! ## Matrix convex combinations (§8.5.1) -/

section MatrixConvexCombo

variable {A₁ A₂ K₁ K₂ : Matrix n n ℂ}

/-- **Book §8.5.1, bullet 1**  "Definition 8.5.1 encompasses
scalar convex combinations because we can take `K₁ = τ^{1/2} I` and
`K₂ = τ̄^{1/2} I`." -/
theorem matrix_convex_combo_scalar {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (A₁ A₂ : Matrix n n ℂ) :
    ((Real.sqrt τ) • (1 : Matrix n n ℂ))ᴴ * ((Real.sqrt τ) • 1) +
        ((Real.sqrt (1 - τ)) • (1 : Matrix n n ℂ))ᴴ *
          ((Real.sqrt (1 - τ)) • 1) = 1 ∧
      ((Real.sqrt τ) • (1 : Matrix n n ℂ))ᴴ * A₁ * ((Real.sqrt τ) • 1) +
        ((Real.sqrt (1 - τ)) • (1 : Matrix n n ℂ))ᴴ * A₂ *
          ((Real.sqrt (1 - τ)) • 1) = τ • A₁ + (1 - τ) • A₂ := by
  have hct : ∀ c : ℝ, (c • (1 : Matrix n n ℂ))ᴴ = c • 1 := by
    intro c
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_one]
  have hprod : ∀ (c : ℝ) (M : Matrix n n ℂ),
      (c • (1 : Matrix n n ℂ)) * M * (c • 1) = (c * c) • M := by
    intro c M
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
      Matrix.mul_one, smul_smul]
  have h2 : ∀ c : ℝ, (c • (1 : Matrix n n ℂ)) * (c • 1) = (c * c) • 1 := by
    intro c
    rw [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul]
  constructor
  · rw [hct, hct, h2, h2, Real.mul_self_sqrt hτ.1,
      Real.mul_self_sqrt (by linarith [hτ.2])]
    module
  · rw [hct, hct, hprod, hprod, Real.mul_self_sqrt hτ.1,
      Real.mul_self_sqrt (by linarith [hτ.2])]

/-- **Book §8.5.1, bullet 2**  "The matrix convex combination preserves the
identity matrix: `K₁ᴴ I K₁ + K₂ᴴ I K₂ = I`." -/
theorem matrix_convex_combo_one (hK : K₁ᴴ * K₁ + K₂ᴴ * K₂ = 1) :
    K₁ᴴ * (1 : Matrix n n ℂ) * K₁ + K₂ᴴ * 1 * K₂ = 1 := by
  rw [Matrix.mul_one, Matrix.mul_one]
  exact hK

/-- **Book §8.5.1, bullet 3**  "The matrix convex combination preserves
positivity." -/
theorem matrix_convex_combo_posSemidef (h₁ : A₁.PosSemidef)
    (h₂ : A₂.PosSemidef) :
    (K₁ᴴ * A₁ * K₁ + K₂ᴴ * A₂ * K₂).PosSemidef :=
  (h₁.conjTranspose_mul_mul_same K₁).add (h₂.conjTranspose_mul_mul_same K₂)

/-- **Book §8.5.1, bullet 4**  "If the eigenvalues of `A₁` and `A₂` are
contained in an interval `I`, then the eigenvalues of the matrix convex
combination are also contained in `I`."  The interval structure enters via
`Set.OrdConnected`. -/
theorem matrix_convex_combo_eigenvalues_mem {I : Set ℝ}
    (hIc : I.OrdConnected) (hA₁ : A₁.IsHermitian) (hA₂ : A₂.IsHermitian)
    (hI₁ : ∀ i, hA₁.eigenvalues i ∈ I) (hI₂ : ∀ i, hA₂.eigenvalues i ∈ I)
    (hK : K₁ᴴ * K₁ + K₂ᴴ * K₂ = 1)
    (hcomb : (K₁ᴴ * A₁ * K₁ + K₂ᴴ * A₂ * K₂).IsHermitian) :
    ∀ i, hcomb.eigenvalues i ∈ I := by
  rcases isEmpty_or_nonempty n with hn | hn
  · intro i
    exact (IsEmpty.false i).elim
  intro i
  set c := min (lambdaMin hA₁) (lambdaMin hA₂) with hc
  set C := max (lambdaMax hA₁) (lambdaMax hA₂) with hC
  -- the two-sided Loewner sandwich of the matrix convex combination
  have hkey : ∀ c' : ℝ, K₁ᴴ * (c' • (1 : Matrix n n ℂ)) * K₁ +
      K₂ᴴ * (c' • 1) * K₂ = c' • (1 : Matrix n n ℂ) := by
    intro c'
    have h1 : ∀ K : Matrix n n ℂ,
        Kᴴ * (c' • (1 : Matrix n n ℂ)) * K = c' • (Kᴴ * K) := by
      intro K
      rw [mul_smul_comm, Matrix.mul_one, smul_mul_assoc]
    rw [h1, h1, ← smul_add, hK]
  have hlow : c • (1 : Matrix n n ℂ) ≤ K₁ᴴ * A₁ * K₁ + K₂ᴴ * A₂ * K₂ := by
    have hlow₁ : c • (1 : Matrix n n ℂ) ≤ A₁ :=
      smul_one_le_of_forall_le hA₁ fun j =>
        le_trans (min_le_left _ _) (lambdaMin_le_eigenvalues hA₁ j)
    have hlow₂ : c • (1 : Matrix n n ℂ) ≤ A₂ :=
      smul_one_le_of_forall_le hA₂ fun j =>
        le_trans (min_le_right _ _) (lambdaMin_le_eigenvalues hA₂ j)
    have h1 := conjugation_rule hlow₁ K₁ᴴ
    have h2 := conjugation_rule hlow₂ K₂ᴴ
    rw [Matrix.conjTranspose_conjTranspose] at h1 h2
    have h3 := add_le_add h1 h2
    rwa [hkey c] at h3
  have hup : K₁ᴴ * A₁ * K₁ + K₂ᴴ * A₂ * K₂ ≤ C • (1 : Matrix n n ℂ) := by
    have hup₁ : A₁ ≤ C • (1 : Matrix n n ℂ) :=
      le_smul_one_of_forall_le hA₁ fun j =>
        le_trans (eigenvalues_le_lambdaMax hA₁ j) (le_max_left _ _)
    have hup₂ : A₂ ≤ C • (1 : Matrix n n ℂ) :=
      le_smul_one_of_forall_le hA₂ fun j =>
        le_trans (eigenvalues_le_lambdaMax hA₂ j) (le_max_right _ _)
    have h1 := conjugation_rule hup₁ K₁ᴴ
    have h2 := conjugation_rule hup₂ K₂ᴴ
    rw [Matrix.conjTranspose_conjTranspose] at h1 h2
    have h3 := add_le_add h1 h2
    rwa [hkey C] at h3
  have h1 := le_eigenvalues_of_smul_one_le hcomb hlow i
  have h2 := eigenvalues_le_of_le_smul_one hcomb hup i
  -- the endpoints are attained eigenvalues, hence lie in `I`
  have hcI : c ∈ I := by
    rcases min_cases (lambdaMin hA₁) (lambdaMin hA₂) with ⟨heq, -⟩ | ⟨heq, -⟩
    · obtain ⟨j, hj⟩ := exists_eigenvalues_eq_lambdaMin hA₁
      rw [hc, heq, ← hj]
      exact hI₁ j
    · obtain ⟨j, hj⟩ := exists_eigenvalues_eq_lambdaMin hA₂
      rw [hc, heq, ← hj]
      exact hI₂ j
  have hCI : C ∈ I := by
    rcases max_cases (lambdaMax hA₁) (lambdaMax hA₂) with ⟨heq, -⟩ | ⟨heq, -⟩
    · obtain ⟨j, hj⟩ := exists_eigenvalues_eq_lambdaMax hA₁
      rw [hC, heq, ← hj]
      exact hI₁ j
    · obtain ⟨j, hj⟩ := exists_eigenvalues_eq_lambdaMax hA₂
      rw [hC, heq, ← hj]
      exact hI₂ j
  exact hIc.out hcI hCI ⟨h1, h2⟩

end MatrixConvexCombo

/-! ## Unitary completion of an isometric column pair -/

section UnitaryCompletion

/-- **Book Theorem 8.5.2 (proof step).**

**Implicit step in the proof of 8.5.2**  "we can choose
`L₁` and `L₂` to complete the unitary matrix `Q`" — an isometric column
pair (`K₁ᴴK₁ + K₂ᴴK₂ = I`) extends to a unitary `Q` whose first column
block is `[K₁; K₂]`.  Recovered proof: the columns form an orthonormal
family; the orthogonal complement of their span has dimension `|n|`, and
an orthonormal basis of it supplies the remaining columns. -/
lemma exists_unitary_completion {K₁ K₂ : Matrix n n ℂ}
    (hK : K₁ᴴ * K₁ + K₂ᴴ * K₂ = 1) :
    ∃ Q : Matrix (n ⊕ n) (n ⊕ n) ℂ,
      Qᴴ * Q = 1 ∧ Q * Qᴴ = 1 ∧
      (∀ i j, Q (Sum.inl i) (Sum.inl j) = K₁ i j) ∧
      (∀ i j, Q (Sum.inr i) (Sum.inl j) = K₂ i j) := by
  classical
  -- the isometric column family
  set vcol : n → EuclideanSpace ℂ (n ⊕ n) := fun j =>
    WithLp.toLp 2 (Sum.elim (fun i => K₁ i j) (fun i => K₂ i j)) with hvcol
  have hvv : ∀ j k, (inner ℂ (vcol j) (vcol k) : ℂ) =
      if j = k then 1 else 0 := by
    intro j k
    rw [inner_eq_star_dotProduct]
    have h1 : star (⇑(vcol j) : n ⊕ n → ℂ) ⬝ᵥ (⇑(vcol k) : n ⊕ n → ℂ) =
        (K₁ᴴ * K₁ + K₂ᴴ * K₂) j k := by
      simp [hvcol, dotProduct, Fintype.sum_sum_type, Matrix.mul_apply,
        Matrix.add_apply, Matrix.conjTranspose_apply]
    rw [h1, hK, Matrix.one_apply]
  have horthv : Orthonormal ℂ vcol := orthonormal_iff_ite.mpr hvv
  -- the orthogonal complement of the span has dimension `|n|`
  set S := Submodule.span ℂ (Set.range vcol) with hS
  have hrankS : Module.finrank ℂ ↥S = Fintype.card n :=
    finrank_span_eq_card horthv.linearIndependent
  have hrankO : Module.finrank ℂ ↥(Sᗮ) = Fintype.card n := by
    have h1 := S.finrank_add_finrank_orthogonal
    rw [hrankS, finrank_euclideanSpace, Fintype.card_sum] at h1
    omega
  have hcard : Fintype.card (Fin (Module.finrank ℂ ↥(Sᗮ))) =
      Fintype.card n := by
    rw [Fintype.card_fin, hrankO]
  set bO := (stdOrthonormalBasis ℂ ↥(Sᗮ)).reindex
    (Fintype.equivOfCardEq hcard) with hbO
  set wcol : n → EuclideanSpace ℂ (n ⊕ n) := fun j =>
    ((bO j : ↥(Sᗮ)) : EuclideanSpace ℂ (n ⊕ n)) with hwcol
  set qcol : n ⊕ n → EuclideanSpace ℂ (n ⊕ n) := Sum.elim vcol wcol
    with hqcol
  -- the full column family is orthonormal
  have hvw : ∀ j k, (inner ℂ (vcol j) (wcol k) : ℂ) = 0 := by
    intro j k
    have h1 : vcol j ∈ S := Submodule.subset_span (Set.mem_range_self j)
    exact ((Submodule.mem_orthogonal S _).mp (bO k).2) (vcol j) h1
  have horth : ∀ a b, (inner ℂ (qcol a) (qcol b) : ℂ) =
      if a = b then 1 else 0 := by
    intro a b
    rcases a with j | j <;> rcases b with k | k
    · rw [hqcol]
      simp only [Sum.elim_inl]
      rw [hvv j k]
      by_cases h : j = k <;> simp [h]
    · rw [hqcol]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hvw j k]
      simp
    · rw [hqcol]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← inner_conj_symm, hvw k j]
      simp
    · rw [hqcol]
      simp only [Sum.elim_inr]
      rw [hwcol]
      rw [show (inner ℂ ((bO j : ↥(Sᗮ)) : EuclideanSpace ℂ (n ⊕ n))
          ((bO k : ↥(Sᗮ)) : EuclideanSpace ℂ (n ⊕ n)) : ℂ) =
          inner ℂ (bO j) (bO k) from (Submodule.coe_inner _ _ _).symm,
        orthonormal_iff_ite.mp bO.orthonormal j k]
      by_cases h : j = k <;> simp [h]
  -- assemble the matrix from the columns
  set Q : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
    Matrix.of (fun p a => (⇑(qcol a) : n ⊕ n → ℂ) p) with hQdef
  have hQ1 : Qᴴ * Q = 1 := by
    ext a b
    have h1 : (Qᴴ * Q) a b =
        star (⇑(qcol a) : n ⊕ n → ℂ) ⬝ᵥ (⇑(qcol b) : n ⊕ n → ℂ) := by
      simp [hQdef, Matrix.mul_apply, dotProduct,
        Matrix.conjTranspose_apply]
    rw [h1, ← inner_eq_star_dotProduct, horth a b, Matrix.one_apply]
  refine ⟨Q, hQ1, Matrix.mul_eq_one_comm.mp hQ1, ?_, ?_⟩
  · intro i j
    show (⇑(qcol (Sum.inl j)) : n ⊕ n → ℂ) (Sum.inl i) = K₁ i j
    rw [hqcol]
    simp [hvcol]
  · intro i j
    show (⇑(qcol (Sum.inl j)) : n ⊕ n → ℂ) (Sum.inr i) = K₂ i j
    rw [hqcol]
    simp [hvcol]

end UnitaryCompletion

/-! ## The (1,1) block of the conjugated block-diagonal matrix -/

section ConjBlock

/-- **Book equation (8.5.5)**  the (1,1) block of `Qᴴ A Q`
(with `A = diag(X, Y)` block diagonal and `Q` having first column block
`[K₁; K₂]`) is the matrix convex combination `K₁ᴴ X K₁ + K₂ᴴ Y K₂`. -/
lemma conj_block_toBlocks₁₁ {Q : Matrix (n ⊕ n) (n ⊕ n) ℂ}
    {K₁ K₂ X Y : Matrix n n ℂ}
    (hQ11 : ∀ i j, Q (Sum.inl i) (Sum.inl j) = K₁ i j)
    (hQ21 : ∀ i j, Q (Sum.inr i) (Sum.inl j) = K₂ i j) :
    (Qᴴ * Matrix.fromBlocks X 0 0 Y * Q).toBlocks₁₁ =
      K₁ᴴ * X * K₁ + K₂ᴴ * Y * K₂ := by
  ext i j
  simp only [Matrix.toBlocks₁₁, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.of_apply,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add, hQ11, hQ21]

end ConjBlock

/-! ## The Operator Jensen Inequality (Theorem 8.5.2) -/

section OperatorJensenMain

/-- **Book Theorem (Operator Jensen Inequality, 8.5.2)**  "Let
`f` be an operator convex function on an interval `I`, and let `A₁` and
`A₂` be Hermitian matrices with eigenvalues in `I`.  Consider a
decomposition of the identity `K₁ᴴK₁ + K₂ᴴK₂ = I`.  Then
`f(K₁ᴴA₁K₁ + K₂ᴴA₂K₂) ≼ K₁ᴴ f(A₁) K₁ + K₂ᴴ f(A₂) K₂`."

Operator convexity is consumed at the doubled index type `n ⊕ n`, the
type where the book's block-matrix proof applies it.

Author note: `OperatorConvexOn` is dimension-indexed, so Lean assumes operator convexity only at the block dimension used by this proof. -/
theorem operator_jensen {f : ℝ → ℝ} {I : Set ℝ}
    (hf : OperatorConvexOn (n ⊕ n) f I)
    {A₁ A₂ K₁ K₂ : Matrix n n ℂ} (hA₁ : A₁.IsHermitian)
    (hA₂ : A₂.IsHermitian)
    (hI₁ : ∀ i, hA₁.eigenvalues i ∈ I) (hI₂ : ∀ i, hA₂.eigenvalues i ∈ I)
    (hK : K₁ᴴ * K₁ + K₂ᴴ * K₂ = 1) :
    cfc f (K₁ᴴ * A₁ * K₁ + K₂ᴴ * A₂ * K₂) ≤
      K₁ᴴ * cfc f A₁ * K₁ + K₂ᴴ * cfc f A₂ * K₂ := by
  obtain ⟨Q, hQ1, hQ2, hQ11, hQ21⟩ := exists_unitary_completion hK
  have hAbher : (Matrix.fromBlocks A₁ 0 0 A₂).IsHermitian :=
    isHermitian_fromBlocks_diag hA₁ hA₂
  set W : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
    Qᴴ * Matrix.fromBlocks A₁ 0 0 A₂ * Q with hW
  have hWher : W.IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul Q hAbher
  -- spectral bookkeeping: everything stays inside `I`
  have hAbspec : spectrum ℝ (Matrix.fromBlocks A₁ 0 0 A₂) ⊆ I := by
    refine spectrum_fromBlocks_diag_subset.trans (Set.union_subset ?_ ?_)
    · exact spectrum_subset_of_eigenvalues_mem hA₁ hI₁
    · exact spectrum_subset_of_eigenvalues_mem hA₂ hI₂
  have hWspec : spectrum ℝ W ⊆ I := by
    rw [hW, spectrum_conj_unitary hQ1 hQ2]
    exact hAbspec
  have hU1 : (blockU n n)ᴴ * blockU n n = 1 := blockU_conj_mul
  have hU2 : blockU n n * (blockU n n)ᴴ = 1 := blockU_mul_conj
  set W' : Matrix (n ⊕ n) (n ⊕ n) ℂ := (blockU n n)ᴴ * W * blockU n n
    with hW'
  have hW'her : W'.IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul (blockU n n) hWher
  have hW'spec : spectrum ℝ W' ⊆ I := by
    rw [hW', spectrum_conj_unitary hU1 hU2]
    exact hWspec
  -- the matrix convex combination is the (1,1) block of `W`
  have hcomb : K₁ᴴ * A₁ * K₁ + K₂ᴴ * A₂ * K₂ = W.toBlocks₁₁ :=
    (conj_block_toBlocks₁₁ hQ11 hQ21).symm
  have hW11her : (W.toBlocks₁₁).IsHermitian := toBlocks₁₁_isHermitian hWher
  have hW22her : (W.toBlocks₂₂).IsHermitian := toBlocks₂₂_isHermitian hWher
  -- the two-point unitary average (8.5.6)
  have havg : (1/2 : ℝ) • W + (1/2 : ℝ) • W' =
      Matrix.fromBlocks (W.toBlocks₁₁) 0 0 (W.toBlocks₂₂) := by
    rw [hW']
    exact half_avg_conj_diag W
  -- operator convexity at `τ = 1/2`
  have h12 : (1 : ℝ) - 1/2 = 1/2 := by norm_num
  have hjensen := hf W W' hWher hW'her
    (eigenvalues_mem_of_spectrum_subset hWher hWspec)
    (eigenvalues_mem_of_spectrum_subset hW'her hW'spec)
    (1/2) ⟨by norm_num, by norm_num⟩
  rw [h12] at hjensen
  -- LHS chain (first three lines of the book's display)
  have hL : cfc f (K₁ᴴ * A₁ * K₁ + K₂ᴴ * A₂ * K₂) =
      (cfc f ((1/2 : ℝ) • W + (1/2 : ℝ) • W')).toBlocks₁₁ := by
    rw [hcomb, havg, cfc_fromBlocks_diag hW11her hW22her f,
      Matrix.toBlocks_fromBlocks₁₁]
  -- RHS chain (the reversal of steps)
  have hcfcW : cfc f W = Qᴴ * cfc f (Matrix.fromBlocks A₁ 0 0 A₂) * Q := by
    rw [hW]
    exact cfc_conj_unitary hAbher hQ1 hQ2 f
  have hcfcW' : cfc f W' = (blockU n n)ᴴ * cfc f W * blockU n n := by
    rw [hW']
    exact cfc_conj_unitary hWher hU1 hU2 f
  have hR : ((1/2 : ℝ) • cfc f W + (1/2 : ℝ) • cfc f W').toBlocks₁₁ =
      K₁ᴴ * cfc f A₁ * K₁ + K₂ᴴ * cfc f A₂ * K₂ := by
    rw [hcfcW', half_avg_conj_diag (cfc f W),
      Matrix.toBlocks_fromBlocks₁₁, hcfcW,
      cfc_fromBlocks_diag hA₁ hA₂ f]
    exact conj_block_toBlocks₁₁ hQ11 hQ21
  calc cfc f (K₁ᴴ * A₁ * K₁ + K₂ᴴ * A₂ * K₂)
      = (cfc f ((1/2 : ℝ) • W + (1/2 : ℝ) • W')).toBlocks₁₁ := hL
    _ ≤ ((1/2 : ℝ) • cfc f W + (1/2 : ℝ) • cfc f W').toBlocks₁₁ :=
        toBlocks₁₁_loewner_mono hjensen
    _ = K₁ᴴ * cfc f A₁ * K₁ + K₂ᴴ * cfc f A₂ * K₂ := hR

end OperatorJensenMain

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# §8.6: The Matrix Perspective Transformation

* **Definition (Matrix Perspective)**  `matrixPerspective f A H` renders
  `Ψ_f(A; H) = A^{1/2}·f(A^{-1/2} H A^{-1/2})·A^{1/2}` using the pd square
  root `posSqrt` established earlier in this module. The book's remark "the Conjugation Rule
  ensures that all the matrices involved remain positive definite, so this
  definition makes sense" is `matrixPerspective_arg_posDef`
  (= `posDef_posSqrt_inv_conj`).
* **Display (8.6.1)**  `matrixPerspective_commute` —
  `Ψ_f(A; H) = A·f(H A⁻¹)` when `A` and `H` commute.  The book's proof
  hint "commuting matrices are simultaneously diagonalizable" is replaced
  by an equivalent implicit-prerequisite recovery: any matrix commuting
  with a Hermitian `M` commutes with every standard matrix function of
  `M` (`commute_cfc`, proved by realizing `f(M)` as an interpolating
  polynomial in `M` via `Lagrange.interpolate`).
* **Theorem (Matrix Perspective is Operator Convex,
  8.6.2)**  `matrixPerspective_operator_convex`,
  proved by the book's matrix interpolation parameters
  `K₁ = τ^{1/2} A₁^{1/2} A^{-1/2}`, `K₂ = τ̄^{1/2} A₂^{1/2} A^{-1/2}` and
  the operator Jensen inequality (consumed at index type `n ⊕ n`).
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A H M X : Matrix n n ℂ}

/-! ## Commutation passes through the functional calculus -/

section CommuteCfc

/-- Lean implementation helper: a matrix commuting with a pd matrix
commutes with its inverse. -/
lemma commute_posDef_inv (hS : M.PosDef) (h : Commute X M) :
    Commute X M⁻¹ := by
  show X * M⁻¹ = M⁻¹ * X
  calc X * M⁻¹ = (M⁻¹ * M) * (X * M⁻¹) := by
        rw [posDef_inv_mul_self hS, Matrix.one_mul]
    _ = M⁻¹ * (M * X) * M⁻¹ := by noncomm_ring
    _ = M⁻¹ * (X * M) * M⁻¹ := by rw [← h.eq]
    _ = (M⁻¹ * X) * (M * M⁻¹) := by noncomm_ring
    _ = M⁻¹ * X := by rw [posDef_mul_inv_self hS, Matrix.mul_one]

/-- **Book equation (8.6.1) (implicit prerequisite).**

**Implicit prerequisite of (8.6.1)**  a matrix that
commutes with a Hermitian matrix `M` commutes with every standard matrix
function of `M`.  Recovered proof: `f(M)` agrees with `p(M)` for a
Lagrange interpolating polynomial `p` through the eigenvalues of `M`, and
polynomials in `M` commute with everything that commutes with `M`.  (This
replaces the book's appeal to simultaneous diagonalization.) -/
lemma commute_cfc (hM : M.IsHermitian) (h : Commute X M) (f : ℝ → ℝ) :
    Commute X (cfc f M) := by
  classical
  set s : Finset ℝ := Finset.image hM.eigenvalues Finset.univ with hs
  set p : Polynomial ℝ := Lagrange.interpolate s id f with hp
  have heval : ∀ i, p.eval (hM.eigenvalues i) = f (hM.eigenvalues i) := by
    intro i
    have h1 : hM.eigenvalues i ∈ s :=
      Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have h2 := Lagrange.eval_interpolate_at_node (r := f)
      (Set.injOn_id _) h1
    rw [hp]
    simpa only [id_eq] using h2
  have hcfc : cfc f M = cfc (fun x => p.eval x) M :=
    cfc_congr_of_eigenvalues hM fun i => (heval i).symm
  have h3 : (fun x : ℝ => p.eval x) =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        fun x : ℝ => p.coeff k * x ^ k := by
    funext x
    rw [Finset.sum_apply]
    exact Polynomial.eval_eq_sum_range x
  have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  have hpoly : cfc (fun x => p.eval x) M =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • M ^ k := by
    rw [h3, cfc_sum _ M _ (fun k _ => continuousOn_matrix_spectrum _ M)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cfc_const_mul (p.coeff k) (fun x : ℝ => x ^ k) M
      (continuousOn_matrix_spectrum _ M), cfc_pow_eq hM k]
  rw [hcfc, hpoly]
  exact Finset.sum_induction _ (Commute X)
    (fun _ _ => Commute.add_right) (Commute.zero_right X)
    fun k _ => (h.pow_right k).smul_right _

end CommuteCfc

/-! ## The matrix perspective (Definition, §8.6.1) -/

section PerspectiveDef

/-- **Book §8.6.1 (definition of the matrix perspective).** Let `f : ℝ_{++} → ℝ` be an
operator convex function, and let `A` and `H` be positive-definite
matrices of the same size.  Define the perspective map
`Ψ_f(A; H) = A^{1/2}·f(A^{-1/2} H A^{-1/2})·A^{1/2}`. (`posSqrt A` is
the book's `A^{1/2}`; its matrix inverse is the book's `A^{-1/2}`.) -/
noncomputable def matrixPerspective (f : ℝ → ℝ) (A H : Matrix n n ℂ) :
    Matrix n n ℂ :=
  posSqrt A * cfc f ((posSqrt A)⁻¹ * H * (posSqrt A)⁻¹) * posSqrt A

/-- **Book remark (§8.6.1)**  "The Conjugation Rule ensures that all the
matrices involved remain positive definite, so this definition makes
sense" — the argument of `f` in the perspective is pd. -/
lemma matrixPerspective_arg_posDef (hA : A.PosDef) (hH : H.PosDef) :
    ((posSqrt A)⁻¹ * H * (posSqrt A)⁻¹).PosDef :=
  posDef_posSqrt_inv_conj hA hH

/-- **Book equation (8.6.1)**  "`Ψ_f(A; H) = A·f(H A⁻¹)` when
`A` and `H` commute." -/
theorem matrixPerspective_commute {f : ℝ → ℝ} (hA : A.PosDef)
    (hH : H.PosDef) (hcomm : Commute A H) :
    matrixPerspective f A H = A * cfc f (H * A⁻¹) := by
  have hcommS : Commute H (posSqrt A) := commute_cfc hA.1 hcomm.symm _
  have hcommSinv : Commute H (posSqrt A)⁻¹ :=
    commute_posDef_inv (posSqrt_posDef hA) hcommS
  -- the argument collapses: `A^{-1/2} H A^{-1/2} = H A⁻¹`
  have harg : (posSqrt A)⁻¹ * H * (posSqrt A)⁻¹ = H * A⁻¹ := by
    calc (posSqrt A)⁻¹ * H * (posSqrt A)⁻¹
        = H * (posSqrt A)⁻¹ * (posSqrt A)⁻¹ := by rw [← hcommSinv.eq]
      _ = H * ((posSqrt A)⁻¹ * (posSqrt A)⁻¹) := by
          rw [Matrix.mul_assoc]
      _ = H * (posSqrt A * posSqrt A)⁻¹ := by rw [Matrix.mul_inv_rev]
      _ = H * A⁻¹ := by rw [posSqrt_mul_self hA.posSemidef]
  rw [matrixPerspective, harg]
  -- `√A` commutes with `f(H A⁻¹)`
  have hcommSA : Commute (posSqrt A) A := (commute_cfc hA.1 (Commute.refl A)
    Real.sqrt).symm
  have hcommSAinv : Commute (posSqrt A) A⁻¹ :=
    commute_posDef_inv hA hcommSA
  have hcommSarg : Commute (posSqrt A) (H * A⁻¹) :=
    Commute.mul_right hcommS.symm hcommSAinv
  have hargher : (H * A⁻¹).IsHermitian := by
    rw [← harg]
    have h1 := Matrix.isHermitian_conjTranspose_mul_mul ((posSqrt A)⁻¹) hH.1
    rwa [(isHermitian_posSqrt_inv hA).eq] at h1
  have hcommSC : Commute (posSqrt A) (cfc f (H * A⁻¹)) :=
    commute_cfc hargher hcommSarg f
  calc posSqrt A * cfc f (H * A⁻¹) * posSqrt A
      = posSqrt A * (cfc f (H * A⁻¹) * posSqrt A) := by
        rw [Matrix.mul_assoc]
    _ = posSqrt A * (posSqrt A * cfc f (H * A⁻¹)) := by
        rw [← hcommSC.eq]
    _ = (posSqrt A * posSqrt A) * cfc f (H * A⁻¹) := by
        rw [Matrix.mul_assoc]
    _ = A * cfc f (H * A⁻¹) := by rw [posSqrt_mul_self hA.posSemidef]

end PerspectiveDef

/-! ## The matrix perspective is operator convex (Theorem
8.6.2) -/

section PerspectiveConvex

/-- **Book Theorem (Matrix Perspective is Operator Convex,
8.6.2)**  "Let `f : ℝ_{++} → ℝ` be an operator
convex function.  Let `Aᵢ` and `Hᵢ` be positive-definite matrices of the
same size.  Then
`Ψ_f(τA₁ + τ̄A₂; τH₁ + τ̄H₂) ≼ τ·Ψ_f(A₁; H₁) + τ̄·Ψ_f(A₂; H₂)` for
`τ ∈ [0,1]`."  Proof via the book's matrix interpolation parameters and
the operator Jensen inequality (consumed at index type `n ⊕ n`).

Author note: the Lean hypothesis is dimension-local (`n ⊕ n`), matching the block dimension consumed by operator Jensen. -/
theorem matrixPerspective_operator_convex {f : ℝ → ℝ}
    (hf : OperatorConvexOn (n ⊕ n) f (Set.Ioi 0))
    {A₁ A₂ H₁ H₂ : Matrix n n ℂ} (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (hH₁ : H₁.PosDef) (hH₂ : H₂.PosDef) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    matrixPerspective f (τ • A₁ + (1 - τ) • A₂) (τ • H₁ + (1 - τ) • H₂) ≤
      τ • matrixPerspective f A₁ H₁ +
        (1 - τ) • matrixPerspective f A₂ H₂ := by
  have hτ' : (0 : ℝ) ≤ 1 - τ := by linarith [hτ.2]
  have hA : (τ • A₁ + (1 - τ) • A₂).PosDef := posDef_convex_combo hA₁ hA₂ hτ
  set SA := posSqrt (τ • A₁ + (1 - τ) • A₂) with hSA
  -- the matrix interpolation parameters
  set K₁ : Matrix n n ℂ := Real.sqrt τ • (posSqrt A₁ * SA⁻¹) with hK₁def
  set K₂ : Matrix n n ℂ := Real.sqrt (1 - τ) • (posSqrt A₂ * SA⁻¹)
    with hK₂def
  have hSAinvh : (SA⁻¹).IsHermitian := by
    rw [hSA]
    exact isHermitian_posSqrt_inv hA
  have hK₁ct : K₁ᴴ = Real.sqrt τ • (SA⁻¹ * posSqrt A₁) := by
    rw [hK₁def, Matrix.conjTranspose_smul, star_trivial,
      Matrix.conjTranspose_mul, hSAinvh.eq, (isHermitian_posSqrt A₁).eq]
  have hK₂ct : K₂ᴴ = Real.sqrt (1 - τ) • (SA⁻¹ * posSqrt A₂) := by
    rw [hK₂def, Matrix.conjTranspose_smul, star_trivial,
      Matrix.conjTranspose_mul, hSAinvh.eq, (isHermitian_posSqrt A₂).eq]
  -- generic sandwich collapse and its two instances
  have hKC : ∀ (c : ℝ), 0 ≤ c → ∀ B C : Matrix n n ℂ,
      (Real.sqrt c • (SA⁻¹ * B)) * C * (Real.sqrt c • (B * SA⁻¹)) =
        c • (SA⁻¹ * (B * C * B) * SA⁻¹) := by
    intro c hc B C
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
      Real.mul_self_sqrt hc]
    congr 1
    noncomm_ring
  have hinner : ∀ {B : Matrix n n ℂ}, B.PosDef → ∀ X : Matrix n n ℂ,
      posSqrt B * ((posSqrt B)⁻¹ * X * (posSqrt B)⁻¹) * posSqrt B = X := by
    intro B hB X
    calc posSqrt B * ((posSqrt B)⁻¹ * X * (posSqrt B)⁻¹) * posSqrt B
        = (posSqrt B * (posSqrt B)⁻¹) * X *
            ((posSqrt B)⁻¹ * posSqrt B) := by noncomm_ring
      _ = X := by
          rw [mul_posSqrt_inv hB, posSqrt_inv_mul hB, Matrix.one_mul,
            Matrix.mul_one]
  have hcollapse : ∀ X : Matrix n n ℂ,
      SA * (SA⁻¹ * X * SA⁻¹) * SA = X := by
    intro X
    calc SA * (SA⁻¹ * X * SA⁻¹) * SA
        = (SA * SA⁻¹) * X * (SA⁻¹ * SA) := by noncomm_ring
      _ = X := by
          rw [hSA, mul_posSqrt_inv hA, posSqrt_inv_mul hA, Matrix.one_mul,
            Matrix.mul_one]
  -- the decomposition of the identity
  have hK₁K₁ : K₁ᴴ * K₁ = τ • (SA⁻¹ * A₁ * SA⁻¹) := by
    rw [hK₁ct, hK₁def, smul_mul_assoc, mul_smul_comm, smul_smul,
      Real.mul_self_sqrt hτ.1]
    congr 1
    calc SA⁻¹ * posSqrt A₁ * (posSqrt A₁ * SA⁻¹)
        = SA⁻¹ * (posSqrt A₁ * posSqrt A₁) * SA⁻¹ := by noncomm_ring
      _ = SA⁻¹ * A₁ * SA⁻¹ := by rw [posSqrt_mul_self hA₁.posSemidef]
  have hK₂K₂ : K₂ᴴ * K₂ = (1 - τ) • (SA⁻¹ * A₂ * SA⁻¹) := by
    rw [hK₂ct, hK₂def, smul_mul_assoc, mul_smul_comm, smul_smul,
      Real.mul_self_sqrt hτ']
    congr 1
    calc SA⁻¹ * posSqrt A₂ * (posSqrt A₂ * SA⁻¹)
        = SA⁻¹ * (posSqrt A₂ * posSqrt A₂) * SA⁻¹ := by noncomm_ring
      _ = SA⁻¹ * A₂ * SA⁻¹ := by rw [posSqrt_mul_self hA₂.posSemidef]
  have hKid : K₁ᴴ * K₁ + K₂ᴴ * K₂ = 1 := by
    rw [hK₁K₁, hK₂K₂]
    have h2 : τ • (SA⁻¹ * A₁ * SA⁻¹) + (1 - τ) • (SA⁻¹ * A₂ * SA⁻¹) =
        SA⁻¹ * (τ • A₁ + (1 - τ) • A₂) * SA⁻¹ := by
      simp only [Matrix.mul_add, Matrix.add_mul, mul_smul_comm,
        smul_mul_assoc]
    rw [h2, hSA]
    exact posSqrt_inv_conj_self hA
  -- the two perspective arguments are pd with spectra in `(0, ∞)`
  have hB₁ : ((posSqrt A₁)⁻¹ * H₁ * (posSqrt A₁)⁻¹).PosDef :=
    posDef_posSqrt_inv_conj hA₁ hH₁
  have hB₂ : ((posSqrt A₂)⁻¹ * H₂ * (posSqrt A₂)⁻¹).PosDef :=
    posDef_posSqrt_inv_conj hA₂ hH₂
  -- the middle identity (third line of the book's first display)
  have hKBK₁ : K₁ᴴ * ((posSqrt A₁)⁻¹ * H₁ * (posSqrt A₁)⁻¹) * K₁ =
      τ • (SA⁻¹ * H₁ * SA⁻¹) := by
    rw [hK₁ct, hK₁def, hKC τ hτ.1, hinner hA₁]
  have hKBK₂ : K₂ᴴ * ((posSqrt A₂)⁻¹ * H₂ * (posSqrt A₂)⁻¹) * K₂ =
      (1 - τ) • (SA⁻¹ * H₂ * SA⁻¹) := by
    rw [hK₂ct, hK₂def, hKC (1 - τ) hτ', hinner hA₂]
  have hmid : SA⁻¹ * (τ • H₁ + (1 - τ) • H₂) * SA⁻¹ =
      K₁ᴴ * ((posSqrt A₁)⁻¹ * H₁ * (posSqrt A₁)⁻¹) * K₁ +
        K₂ᴴ * ((posSqrt A₂)⁻¹ * H₂ * (posSqrt A₂)⁻¹) * K₂ := by
    rw [hKBK₁, hKBK₂]
    simp only [Matrix.mul_add, Matrix.add_mul, mul_smul_comm,
      smul_mul_assoc]
  -- the operator Jensen inequality
  have hjensen := operator_jensen hf hB₁.1 hB₂.1
    (fun i => hB₁.eigenvalues_pos i) (fun i => hB₂.eigenvalues_pos i) hKid
  rw [← hmid] at hjensen
  -- conjugate by `SA = A^{1/2}` (the Conjugation Rule)
  have hconj := conjugation_rule hjensen SA
  have hSAh : SAᴴ = SA := by
    rw [hSA]
    exact (isHermitian_posSqrt _).eq
  rw [hSAh] at hconj
  -- identify the two sides
  have hL : SA * cfc f (SA⁻¹ * (τ • H₁ + (1 - τ) • H₂) * SA⁻¹) * SA =
      matrixPerspective f (τ • A₁ + (1 - τ) • A₂)
        (τ • H₁ + (1 - τ) • H₂) := by
    rw [hSA]
    rfl
  have hR : SA * (K₁ᴴ * cfc f ((posSqrt A₁)⁻¹ * H₁ * (posSqrt A₁)⁻¹) * K₁ +
      K₂ᴴ * cfc f ((posSqrt A₂)⁻¹ * H₂ * (posSqrt A₂)⁻¹) * K₂) * SA =
      τ • matrixPerspective f A₁ H₁ +
        (1 - τ) • matrixPerspective f A₂ H₂ := by
    rw [hK₁ct, hK₁def, hK₂ct, hK₂def, hKC τ hτ.1, hKC (1 - τ) hτ',
      Matrix.mul_add, Matrix.add_mul, mul_smul_comm, mul_smul_comm,
      smul_mul_assoc, smul_mul_assoc, hcollapse, hcollapse]
    rfl
  rw [← hL, ← hR]
  exact hconj

end PerspectiveConvex

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# §8.7: The Kronecker Product

* **Definition (Kronecker Product)**  rendered by Mathlib's `⊗ₖ`
  (`Matrix.kroneckerMap (· * ·)`, indexed by `n × n`);
  `isHermitian_kronecker` records the book's remark that the Kronecker
  product of Hermitian matrices is Hermitian.
* **§8.7.2 linearity bullets**  `kronecker_zero_left`,
  `kronecker_zero_right`, `kronecker_real_smul_left`,
  `kronecker_real_smul_right`, `kronecker_add_left`,
  `kronecker_add_right` (Mathlib correspondences).
* **Display (8.7.1)**  `kronecker_mixed_product`
  (= `Matrix.mul_kronecker_mul`).
* **Display (8.7.2)**  `kronecker_inv`.
* **Display (8.7.3)**  `kronecker_one_comm`.
* **Fact (Kronecker Product Preserves Positivity)**  `posDef_kronecker`
  (the book's square-root proof).
* **Fact (Logarithm of a Kronecker Product, 8.7.3)** 
  `log_kronecker`, via the book's exponential route (`exp` of a commuting
  sum, `exp` through the algebra homomorphisms `· ⊗ₖ 1` and `1 ⊗ₖ ·`).
* **§8.7.6 "A Linear Map" — with repair SI-C8-1**  over `ℂ`, the source's
  claims `φ(A ⊗ H) = tr(AH)`, `φ(M) = ι†Mι` (`ι = vec(I)`), and
  (8.7.5) are mutually inconsistent: the quadratic form
  `ι†(A ⊗ₖ H)ι` equals `tr(AᵀH)`, not `tr(AH)`, and the
  `tr(AH)`-functional does *not* preserve positivity.  We formalize the
  positive functional `phiMap M = ι†Mι` (the book's displayed
  representation), prove `phiMap (A ⊗ₖ H) = (Aᵀ * H).trace`
  (`phiMap_kronecker`), positivity (`phiMap_nonneg`,
  `phiMap_loewner_mono`, and the book's display (8.7.5) as
  `phiMap_sum_nonneg`), and record the refutation of the printed formula
  (`si_c8_1_refutation`, witness `A = H = σ_y`). The §8.8 development
  below uses the corresponding transpose repair.
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A H M : Matrix n n ℂ}

/-! ## Hermitian structure and linearity (§8.7.1–§8.7.2) -/

section KroneckerBasics

/-- **Book §8.7.1 (definition of the Kronecker product).** The Kronecker
product `A ⊗ H` is the `d² × d²` Hermitian matrix […]; the Kronecker
product of Hermitian matrices is Hermitian. -/
lemma isHermitian_kronecker (hA : A.IsHermitian) (hH : H.IsHermitian) :
    (A ⊗ₖ H).IsHermitian := by
  show (A ⊗ₖ H)ᴴ = A ⊗ₖ H
  rw [Matrix.conjTranspose_kronecker, hA.eq, hH.eq]

/-- **Book §8.7.2, display 1 (left half)**  "`0 ⊗ H = 0`". -/
theorem kronecker_zero_left (H : Matrix n n ℂ) :
    (0 : Matrix n n ℂ) ⊗ₖ H = 0 := Matrix.zero_kronecker H

/-- **Book §8.7.2, display 1 (right half)**  "`A ⊗ 0 = 0`". -/
theorem kronecker_zero_right (A : Matrix n n ℂ) :
    A ⊗ₖ (0 : Matrix n n ℂ) = 0 := Matrix.kronecker_zero A

/-- **Book §8.7.2, display 2 (left half)**  "`(αA) ⊗ H = α(A ⊗ H)` for
`α ∈ ℝ`". -/
theorem kronecker_real_smul_left (α : ℝ) (A H : Matrix n n ℂ) :
    (α • A) ⊗ₖ H = α • (A ⊗ₖ H) := Matrix.smul_kronecker α A H

/-- **Book §8.7.2, display 2 (right half)**  "`α(A ⊗ H) = A ⊗ (αH)` for
`α ∈ ℝ`". -/
theorem kronecker_real_smul_right (α : ℝ) (A H : Matrix n n ℂ) :
    A ⊗ₖ (α • H) = α • (A ⊗ₖ H) := Matrix.kronecker_smul α A H

/-- **Book §8.7.2, display 3 (left half)**  "`(A₁ + A₂) ⊗ H = A₁⊗H + A₂⊗H`". -/
theorem kronecker_add_left (A₁ A₂ H : Matrix n n ℂ) :
    (A₁ + A₂) ⊗ₖ H = A₁ ⊗ₖ H + A₂ ⊗ₖ H := Matrix.add_kronecker A₁ A₂ H

/-- **Book §8.7.2, display 3 (right half)**  "`A ⊗ (H₁ + H₂) = A⊗H₁ + A⊗H₂`". -/
theorem kronecker_add_right (A H₁ H₂ : Matrix n n ℂ) :
    A ⊗ₖ (H₁ + H₂) = A ⊗ₖ H₁ + A ⊗ₖ H₂ := Matrix.kronecker_add A H₁ H₂

end KroneckerBasics

/-! ## Mixed products, inverses, commutation (§8.7.3) -/

section MixedProducts

/-- **Book equation (8.7.1)**  "`(A₁ ⊗ H₁)(A₂ ⊗ H₂) =
(A₁A₂) ⊗ (H₁H₂)`" (Mathlib correspondence:
`Matrix.mul_kronecker_mul`). -/
theorem kronecker_mixed_product (A₁ H₁ A₂ H₂ : Matrix n n ℂ) :
    (A₁ ⊗ₖ H₁) * (A₂ ⊗ₖ H₂) = (A₁ * A₂) ⊗ₖ (H₁ * H₂) :=
  (Matrix.mul_kronecker_mul A₁ A₂ H₁ H₂).symm

/-- **Book equation (8.7.2)**  "`(A ⊗ H)⁻¹ = A⁻¹ ⊗ H⁻¹` when `A`
and `H` are invertible." -/
theorem kronecker_inv (hA : IsUnit A) (hH : IsUnit H) :
    (A ⊗ₖ H)⁻¹ = A⁻¹ ⊗ₖ H⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.mul_kronecker_mul,
    Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA),
    Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det H).mp hH),
    Matrix.one_kronecker_one]

/-- **Book equation (8.7.3)**  "`(A ⊗ I)(I ⊗ H) = (I ⊗ H)(A ⊗ I)` for
all Hermitian matrices `A` and `H`" (proved here for all matrices; both
sides equal `A ⊗ H`). -/
theorem kronecker_one_comm (A H : Matrix n n ℂ) :
    Commute (A ⊗ₖ (1 : Matrix n n ℂ)) ((1 : Matrix n n ℂ) ⊗ₖ H) := by
  show _ * _ = _ * _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

end MixedProducts

/-! ## Positivity (§8.7.4) -/

section KroneckerPositivity

/-- **Book §8.7.4 (Kronecker products preserve positivity).** Let `A` and `H` be
positive-definite matrices. Then `A ⊗ H` is positive definite, via the
book's square-root factorization `A ⊗ H = (A^{1/2} ⊗ H^{1/2})²` and the
determinant of a Kronecker product. -/
theorem posDef_kronecker (hA : A.PosDef) (hH : H.PosDef) :
    (A ⊗ₖ H).PosDef := by
  have h1 : A ⊗ₖ H = (posSqrt A ⊗ₖ posSqrt H) * (posSqrt A ⊗ₖ posSqrt H) := by
    rw [← Matrix.mul_kronecker_mul, posSqrt_mul_self hA.posSemidef,
      posSqrt_mul_self hH.posSemidef]
  have h2 : (posSqrt A ⊗ₖ posSqrt H).IsHermitian :=
    isHermitian_kronecker (isHermitian_posSqrt A) (isHermitian_posSqrt H)
  have h3 : (posSqrt A ⊗ₖ posSqrt H).det ≠ 0 := by
    rw [Matrix.det_kronecker]
    have h4 : (posSqrt A).det ≠ 0 := isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det _).mp (posSqrt_posDef hA).isUnit)
    have h5 : (posSqrt H).det ≠ 0 := isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det _).mp (posSqrt_posDef hH).isUnit)
    exact mul_ne_zero (pow_ne_zero _ h4) (pow_ne_zero _ h5)
  rw [h1]
  exact posDef_sq_of_det_ne_zero h2 h3

end KroneckerPositivity

/-! ## The logarithm of a Kronecker product (§8.7.5) -/

section KroneckerLog

/-- Lean implementation helper: `M ↦ M ⊗ₖ 1` is a `ℂ`-algebra
homomorphism (the structure behind the book's power-series computation
`exp(M ⊗ I) = e^M ⊗ I`). -/
noncomputable def kroneckerLeftAlgHom (n : Type*) [Fintype n]
    [DecidableEq n] : Matrix n n ℂ →ₐ[ℂ] Matrix (n × n) (n × n) ℂ where
  toFun := fun M => M ⊗ₖ (1 : Matrix n n ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' := fun M N => by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := Matrix.zero_kronecker _
  map_add' := fun M N => Matrix.add_kronecker M N _
  commutes' := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_kronecker, Matrix.one_kronecker_one]

/-- Lean implementation helper: `M ↦ 1 ⊗ₖ M` is a `ℂ`-algebra
homomorphism. -/
noncomputable def kroneckerRightAlgHom (n : Type*) [Fintype n]
    [DecidableEq n] : Matrix n n ℂ →ₐ[ℂ] Matrix (n × n) (n × n) ℂ where
  toFun := fun M => (1 : Matrix n n ℂ) ⊗ₖ M
  map_one' := Matrix.one_kronecker_one
  map_mul' := fun M N => by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := Matrix.kronecker_zero _
  map_add' := fun M N => Matrix.kronecker_add _ M N
  commutes' := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Matrix.kronecker_smul, Matrix.one_kronecker_one]

/-- **Book display (proof of 8.7.3)** 
"`exp(M ⊗ I) = e^M ⊗ I`" — the power-series computation, rendered through
the continuous algebra homomorphism `· ⊗ₖ 1`. -/
lemma exp_kronecker_one (M : Matrix n n ℂ) :
    NormedSpace.exp (M ⊗ₖ (1 : Matrix n n ℂ)) =
      (NormedSpace.exp M) ⊗ₖ (1 : Matrix n n ℂ) := by
  have hcont : Continuous (kroneckerLeftAlgHom n) :=
    (kroneckerLeftAlgHom n).toLinearMap.continuous_of_finiteDimensional
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (kroneckerLeftAlgHom n)
    hcont M
    ((NormedSpace.expSeries_radius_eq_top ℂ (Matrix n n ℂ)).symm ▸
      edist_lt_top _ _)
  simpa [kroneckerLeftAlgHom] using h.symm

/-- **Book remark (proof of 8.7.3)**  "a similar calculation
shows that `exp(I ⊗ T) = I ⊗ e^T`." -/
lemma exp_one_kronecker (M : Matrix n n ℂ) :
    NormedSpace.exp ((1 : Matrix n n ℂ) ⊗ₖ M) =
      (1 : Matrix n n ℂ) ⊗ₖ (NormedSpace.exp M) := by
  have hcont : Continuous (kroneckerRightAlgHom n) :=
    (kroneckerRightAlgHom n).toLinearMap.continuous_of_finiteDimensional
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (kroneckerRightAlgHom n)
    hcont M
    ((NormedSpace.expSeries_radius_eq_top ℂ (Matrix n n ℂ)).symm ▸
      edist_lt_top _ _)
  simpa [kroneckerRightAlgHom] using h.symm

/-- Lean implementation helper: `exp(log A) = A` for pd `A` (the book's
"the matrix logarithm is the functional inverse of the matrix
exponential"), reproved here from `cfc_comp`. -/
lemma exp_log_eq_self (hA : A.PosDef) :
    NormedSpace.exp (CFC.log A) = A := by
  have hlogher : (CFC.log A).IsHermitian := isHermitian_cfc _ _
  have hsa : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA.1
  rw [matrixExp_eq_cfc hlogher, CFC.log,
    ← cfc_comp Real.exp Real.log A hsa
      (continuousOn_of_finite (Matrix.finite_real_spectrum.image _) _)
      (continuousOn_matrix_spectrum _ A)]
  have h1 : cfc (Real.exp ∘ Real.log) A = cfc (id : ℝ → ℝ) A := by
    refine cfc_congr_of_eigenvalues hA.1 fun i => ?_
    simp only [Function.comp_apply, id_eq]
    exact Real.exp_log (hA.eigenvalues_pos i)
  rw [h1, cfc_id ℝ A]

/-- **Book Fact (Logarithm of a Kronecker Product, 8.7.3)**  "Let `A`
and `H` be positive-definite matrices.  Then
`log(A ⊗ H) = (log A) ⊗ I + I ⊗ (log H)`" — via the book's exponential
route. -/
theorem log_kronecker (hA : A.PosDef) (hH : H.PosDef) :
    CFC.log (A ⊗ₖ H) =
      (CFC.log A) ⊗ₖ (1 : Matrix n n ℂ) +
        (1 : Matrix n n ℂ) ⊗ₖ (CFC.log H) := by
  have hXher : ((CFC.log A) ⊗ₖ (1 : Matrix n n ℂ) +
      (1 : Matrix n n ℂ) ⊗ₖ (CFC.log H)).IsHermitian :=
    (isHermitian_kronecker (isHermitian_cfc _ _)
      Matrix.isHermitian_one).add
      (isHermitian_kronecker Matrix.isHermitian_one (isHermitian_cfc _ _))
  have hcomm : Commute ((CFC.log A) ⊗ₖ (1 : Matrix n n ℂ))
      ((1 : Matrix n n ℂ) ⊗ₖ (CFC.log H)) := kronecker_one_comm _ _
  have hexp : NormedSpace.exp ((CFC.log A) ⊗ₖ (1 : Matrix n n ℂ) +
      (1 : Matrix n n ℂ) ⊗ₖ (CFC.log H)) = A ⊗ₖ H := by
    rw [NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm
        ((NormedSpace.expSeries_radius_eq_top ℂ
          (Matrix (n × n) (n × n) ℂ)).symm ▸ edist_lt_top _ _)
        ((NormedSpace.expSeries_radius_eq_top ℂ
          (Matrix (n × n) (n × n) ℂ)).symm ▸ edist_lt_top _ _),
      exp_kronecker_one,
      exp_one_kronecker, exp_log_eq_self hA, exp_log_eq_self hH,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  calc CFC.log (A ⊗ₖ H)
      = CFC.log (NormedSpace.exp ((CFC.log A) ⊗ₖ (1 : Matrix n n ℂ) +
          (1 : Matrix n n ℂ) ⊗ₖ (CFC.log H))) := by rw [hexp]
    _ = _ := log_exp_eq hXher

end KroneckerLog

/-! ## The linear map `φ` (§8.7.6, with repair SI-C8-1) -/

section PhiMap

/-- Lean implementation helper.

The vector `ι = vec(I_d)`: the entries of the identity matrix stacked
into a vector of length `d²`. -/
def vecId (n : Type*) [DecidableEq n] : n × n → ℂ :=
  fun p => if p.1 = p.2 then 1 else 0

/-- **Book §8.7.6, the book's displayed representation**
`φ(M) = ι†Mι` with `ι = vec(I)` — taken here as the *definition* of the
functional (repair SI-C8-1: over `ℂ`, this positive functional does
**not** equal `M = A ⊗ H ↦ tr(AH)`; see `phiMap_kronecker` and
`si_c8_1_refutation`).

Author note: over `ℂ`, the book’s printed `tr(AH)` identity is incompatible with `φ(M)=ι†Mι`; this development uses the necessary transpose repair. -/
noncomputable def phiMap (M : Matrix (n × n) (n × n) ℂ) : ℂ :=
  star (vecId n) ⬝ᵥ (M *ᵥ vecId n)

/-- **Book equation (8.7.4), repaired (SI-C8-1)**  on Kronecker products
the functional `φ(M) = ι†Mι` evaluates to `tr(AᵀH)` — not the source's
printed `tr(AH)`, which is incompatible with the `ι`-representation over
`ℂ`.

Author note: over `ℂ`, the correct evaluation is `tr(AᵀH)`; the printed `tr(AH)` formula is valid without repair only in the real-symmetric setting. -/
theorem phiMap_kronecker (A H : Matrix n n ℂ) :
    phiMap (A ⊗ₖ H) = (Aᵀ * H).trace := by
  rw [phiMap, Matrix.trace]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, vecId,
    Pi.star_apply, Matrix.kroneckerMap_apply, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.transpose_apply, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul, apply_ite (star : ℂ → ℂ), star_one,
    star_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]

/-- **Book §8.7.6**  "the map `φ` is linear" — additivity. -/
lemma phiMap_add (X Y : Matrix (n × n) (n × n) ℂ) :
    phiMap (X + Y) = phiMap X + phiMap Y := by
  rw [phiMap, phiMap, phiMap, Matrix.add_mulVec, dotProduct_add]

/-- **Book §8.7.6**  "the map `φ` is linear" — real homogeneity. -/
lemma phiMap_real_smul (c : ℝ) (X : Matrix (n × n) (n × n) ℂ) :
    phiMap (c • X) = c • phiMap X := by
  rw [phiMap, phiMap, Matrix.smul_mulVec, dotProduct_smul]

/-- Lean implementation helper: `φ` of a difference. -/
lemma phiMap_sub (X Y : Matrix (n × n) (n × n) ℂ) :
    phiMap (X - Y) = phiMap X - phiMap Y := by
  rw [phiMap, phiMap, phiMap, Matrix.sub_mulVec, dotProduct_sub]

/-- Lean implementation helper: `φ` of a finite sum. -/
lemma phiMap_sum {ι : Type*} (s : Finset ι)
    (F : ι → Matrix (n × n) (n × n) ℂ) :
    phiMap (∑ i ∈ s, F i) = ∑ i ∈ s, phiMap (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phiMap]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, phiMap_add, ih]

/-- Lean implementation helper: `φ` is nonnegative on psd matrices (the
quadratic-form representation makes this immediate). -/
lemma phiMap_nonneg {X : Matrix (n × n) (n × n) ℂ} (hX : X.PosSemidef) :
    0 ≤ phiMap X :=
  hX.dotProduct_mulVec_nonneg (vecId n)

/-- **Book equation (8.7.5), pairwise form**  `φ` preserves the
semidefinite order. -/
theorem phiMap_loewner_mono {X Y : Matrix (n × n) (n × n) ℂ}
    (h : X ≤ Y) : phiMap X ≤ phiMap Y := by
  have h1 := phiMap_nonneg (X := Y - X) (Matrix.le_iff.mp h)
  rw [phiMap_sub] at h1
  exact sub_nonneg.mp h1

/-- **Book equation (8.7.5)**  "`Σᵢ Aᵢ ⊗ Hᵢ ≽ 0` implies
`Σᵢ φ(Aᵢ ⊗ Hᵢ) ≥ 0`.  This formula is valid for all Hermitian matrices
`Aᵢ` and `Hᵢ`" (proved here for all matrices). -/
theorem phiMap_sum_nonneg {ι : Type*} (s : Finset ι)
    (Am Hm : ι → Matrix n n ℂ)
    (hpsd : (0 : Matrix (n × n) (n × n) ℂ) ≤ ∑ i ∈ s, (Am i) ⊗ₖ (Hm i)) :
    0 ≤ ∑ i ∈ s, phiMap ((Am i) ⊗ₖ (Hm i)) := by
  rw [← phiMap_sum]
  refine phiMap_nonneg ?_
  have h1 := Matrix.le_iff.mp hpsd
  rwa [sub_zero] at h1

/-- Lean implementation helper.

**SI-C8-1 (source error, refutation)**  over `ℂ`, the source's printed
formula `φ(A ⊗ H) = tr(AH)` (8.7.4) is incompatible with the
source's own representation `φ(M) = ι†Mι`: for `A = H = σ_y` the
representation gives `tr(σ_yᵀ σ_y) = −2`, whereas `tr(σ_y²) = 2`.  (The
printed formula is correct for real symmetric matrices only.) -/
theorem si_c8_1_refutation :
    ∃ (A H : Matrix (Fin 2) (Fin 2) ℂ), A.IsHermitian ∧ H.IsHermitian ∧
      phiMap (A ⊗ₖ H) ≠ (A * H).trace := by
  refine ⟨!![0, -Complex.I; Complex.I, 0],
    !![0, -Complex.I; Complex.I, 0], ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Complex.conj_I]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Complex.conj_I]
  · rw [phiMap_kronecker]
    have h1 : ((!![0, -Complex.I; Complex.I, 0] :
        Matrix (Fin 2) (Fin 2) ℂ)ᵀ *
          !![0, -Complex.I; Complex.I, 0]).trace = -2 := by
      rw [Matrix.trace_fin_two]
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
        Complex.I_mul_I]
      norm_num
    have h2 : ((!![0, -Complex.I; Complex.I, 0] :
        Matrix (Fin 2) (Fin 2) ℂ) *
          !![0, -Complex.I; Complex.I, 0]).trace = 2 := by
      rw [Matrix.trace_fin_two]
      simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
      norm_num
    rw [h1, h2]
    norm_num

end PhiMap

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# §8.8: The Matrix Relative Entropy is Convex

* `operatorConvexOn_entropyKernel`: the book's "the function
  `f(a) = a − 1 − log a` is operator convex because it is the sum of the
  affine function `a ↦ a − 1` and the operator convex function
  `a ↦ −log a`".
* `cfc_transpose`, `log_transpose`, `log_posDef_inv`,
  `cfc_entropy_kernel`: supporting matrix-function algebra (the book's
  "`log(A⁻¹) = −log A`" and the entrywise expansion of `f`).
* **Display (8.8.1), repaired (SI-C8-1)** 
  `phi_perspective_eq_mre_trace` — the perspective is evaluated at the
  commuting pair `(A ⊗ I; I ⊗ Hᵀ)` (note the transpose!), so that the
  positive functional `phiMap = ι†(·)ι` recovers exactly
  `tr[A log A − A log H − (A − H)]`.  With the source's printed pair
  `(A ⊗ I; I ⊗ H)` and the printed formula `φ(A ⊗ H) = tr(AH)`, the
  computation is invalid over `ℂ` (see `si_c8_1_refutation` above); the
  transpose repair restores every step, because
  `H ↦ Hᵀ` preserves positive definiteness and convex combinations.
* **Theorem (8.1.4)**  `mre_convex` — the matrix relative
  entropy is (jointly) convex.  This is the final ingredient of the
  proof of Lieb's theorem later in this module.
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A H M : Matrix n n ℂ}

/-! ## The entropy kernel is operator convex -/

section EntropyKernel

/-- Lean implementation helper: operator convexity restricts to smaller
sets. -/
lemma OperatorConvexOn.mono {m : Type*} [Fintype m] [DecidableEq m]
    {f : ℝ → ℝ} {I I' : Set ℝ} (h : OperatorConvexOn m f I)
    (hsub : I' ⊆ I) : OperatorConvexOn m f I' :=
  fun A H hA hH hAI hHI τ hτ =>
    h A H hA hH (fun i => hsub (hAI i)) (fun i => hsub (hHI i)) τ hτ

/-- **Book §8.8, opening argument**  "Consider the function
`f(a) = a − 1 − log a`, defined on the positive real line.  This function
is operator convex because it is the sum of the affine function
`a ↦ a − 1` and the operator convex function `a ↦ −log a`." -/
theorem operatorConvexOn_entropyKernel (m : Type*) [Fintype m]
    [DecidableEq m] :
    OperatorConvexOn m (fun a => a - 1 - Real.log a) (Set.Ioi 0) := by
  have haff : OperatorConvexOn m (fun a : ℝ => a - 1) (Set.Ioi 0) := by
    have h1 := operatorConvexOn_quadratic m (α := -1) (β := 1) (γ := 0)
      le_rfl
    have h2 : (fun t : ℝ => -1 + 1 * t + 0 * t ^ 2) =
        fun a : ℝ => a - 1 := by
      funext t
      ring
    rw [h2] at h1
    exact h1.mono (Set.subset_univ _)
  have hlog : OperatorConvexOn m (fun a : ℝ => -Real.log a) (Set.Ioi 0) :=
    operatorConcaveOn_log m
  have hsum := operatorConvexOn_add haff hlog
  have h3 : (fun a : ℝ => (fun a : ℝ => a - 1) a +
      (fun a : ℝ => -Real.log a) a) = fun a : ℝ => a - 1 - Real.log a := by
    funext a
    ring
  rw [h3] at hsum
  exact hsum

end EntropyKernel

/-! ## Matrix-function algebra: transposes, inverses, and the kernel -/

section FunctionAlgebra

/-- Lean implementation helper (SI-C8-1 repair): standard matrix functions
commute with the transpose, `f(Mᵀ) = f(M)ᵀ`. -/
lemma cfc_transpose (hM : M.IsHermitian) (f : ℝ → ℝ) :
    cfc f Mᵀ = (cfc f M)ᵀ := by
  have hMt : (Mᵀ).IsHermitian := hM.transpose
  set V := (hM.eigenvectorUnitary : Matrix n n ℂ) with hV
  set W := V.map (starRingEnd ℂ) with hWdef
  have hWct : Wᴴ = Vᵀ := by
    ext i j
    simp [hWdef, Matrix.conjTranspose_apply, Matrix.map_apply,
      Matrix.transpose_apply]
  have hVct : (Vᴴ)ᵀ = W := by
    ext i j
    simp [hWdef, Matrix.conjTranspose_apply, Matrix.map_apply,
      Matrix.transpose_apply]
  have hVV : V * Vᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.2
    simpa [star_eq_conjTranspose] using h
  have hWu : W ∈ Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, hWct, ← hVct,
      ← Matrix.transpose_mul, hVV, Matrix.transpose_one]
  have hdec : Mᵀ = W *
      Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) * Wᴴ := by
    conv_lhs => rw [spectral_decomposition hM]
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.diagonal_transpose, hVct, ← hWct, Matrix.mul_assoc]
  rw [cfc_unitary_diagonal hMt hWu hdec f, cfc_eq_book_formula hM f,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
    hVct, ← hWct, Matrix.mul_assoc]

/-- Lean implementation helper (SI-C8-1 repair): `log(Mᵀ) = (log M)ᵀ`. -/
lemma log_transpose (hM : M.IsHermitian) :
    CFC.log Mᵀ = (CFC.log M)ᵀ :=
  cfc_transpose hM Real.log

/-- **Book step (§8.8)**  "`log(A⁻¹) = −log A`" for pd `A`. -/
lemma log_posDef_inv (hA : A.PosDef) : CFC.log A⁻¹ = -CFC.log A := by
  have hsa : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA.1
  rw [inv_eq_cfc hA, CFC.log,
    ← cfc_comp Real.log (fun a : ℝ => a⁻¹) A hsa
      (continuousOn_of_finite (Matrix.finite_real_spectrum.image _) _)
      (continuousOn_matrix_spectrum _ A)]
  have h1 : cfc (Real.log ∘ fun a : ℝ => a⁻¹) A =
      cfc (fun a : ℝ => -Real.log a) A :=
    cfc_congr_of_eigenvalues hA.1 fun i => by
      simp [Real.log_inv]
  rw [h1, cfc_neg, CFC.log]

/-- **Book step (§8.8)**  "introducing the definition of the function
`f`" — `f(K) = K − I − log K` for the entropy kernel
`f(a) = a − 1 − log a`. -/
lemma cfc_entropy_kernel {m : Type*} [Fintype m] [DecidableEq m]
    {K : Matrix m m ℂ} (hK : K.IsHermitian) :
    cfc (fun a : ℝ => a - 1 - Real.log a) K = K - 1 - CFC.log K := by
  have hsa : IsSelfAdjoint K := Matrix.isHermitian_iff_isSelfAdjoint.mp hK
  have h1 := cfc_sub (fun a : ℝ => a - 1) Real.log K
    (continuousOn_matrix_spectrum _ K) (continuousOn_matrix_spectrum _ K)
  rw [show (fun a : ℝ => a - 1 - Real.log a) =
    fun a : ℝ => (fun a : ℝ => a - 1) a - Real.log a from rfl, h1]
  have h2 := cfc_sub (id : ℝ → ℝ) (fun _ : ℝ => (1 : ℝ)) K
    (continuousOn_matrix_spectrum _ K) (continuousOn_matrix_spectrum _ K)
  rw [show (fun a : ℝ => a - 1) =
    fun a : ℝ => id a - (fun _ : ℝ => (1 : ℝ)) a from rfl, h2,
    cfc_id ℝ K, cfc_const_one ℝ K, CFC.log]

/-- Lean implementation helper: the Kronecker product distributes over
negation in the left factor. -/
lemma kronecker_neg_left (X Y : Matrix n n ℂ) :
    (-X) ⊗ₖ Y = -(X ⊗ₖ Y) := by
  rw [show -X = (-1 : ℂ) • X by rw [neg_one_smul], Matrix.smul_kronecker,
    neg_one_smul]

end FunctionAlgebra

/-! ## The `φ ∘ Ψ_f` computation (display (8.8.1), repaired) -/

section PhiPsi

/-- **Book equation (8.8.1), repaired (SI-C8-1)**  evaluating the matrix
perspective of the entropy kernel at the commuting pd pair
`(A ⊗ I; I ⊗ Hᵀ)` and applying the positive functional `φ = ι†(·)ι`
yields exactly `tr[A log A − A log H − (A − H)]` — the matrix relative
entropy `D(A; H)` as a complex trace.  (The transpose on `H` is the
repair: with the source's `I ⊗ H` the functional produces `tr(Aᵀ log H)`
-type terms that do not assemble to `D(A; H)` over `ℂ`.)

Author note: the transpose on `H` repairs the book’s complex-field computation while preserving positive definiteness and convex combinations. -/
theorem phi_perspective_eq_mre_trace (hA : A.PosDef) (hH : H.PosDef) :
    phiMap (matrixPerspective (fun a => a - 1 - Real.log a)
        (A ⊗ₖ (1 : Matrix n n ℂ)) ((1 : Matrix n n ℂ) ⊗ₖ Hᵀ)) =
      (A * (CFC.log A - CFC.log H) - (A - H)).trace := by
  have hA1 : (A ⊗ₖ (1 : Matrix n n ℂ)).PosDef :=
    posDef_kronecker hA Matrix.PosDef.one
  have hHt : (Hᵀ).PosDef := hH.transpose
  have h1Ht : ((1 : Matrix n n ℂ) ⊗ₖ Hᵀ).PosDef :=
    posDef_kronecker Matrix.PosDef.one hHt
  rw [matrixPerspective_commute hA1 h1Ht (kronecker_one_comm A Hᵀ)]
  have h2 : ((1 : Matrix n n ℂ) ⊗ₖ Hᵀ) * (A ⊗ₖ (1 : Matrix n n ℂ))⁻¹ =
      A⁻¹ ⊗ₖ Hᵀ := by
    rw [kronecker_inv hA.isUnit isUnit_one, inv_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [h2]
  have hK : (A⁻¹ ⊗ₖ Hᵀ).PosDef := posDef_kronecker hA.inv hHt
  rw [cfc_entropy_kernel hK.1, log_kronecker hA.inv hHt, log_posDef_inv hA,
    log_transpose hH.1, kronecker_neg_left]
  -- expand into a signed sum of Kronecker products
  have hX : (A ⊗ₖ (1 : Matrix n n ℂ)) *
      ((A⁻¹ ⊗ₖ Hᵀ) - 1 -
        (-((CFC.log A) ⊗ₖ (1 : Matrix n n ℂ)) +
          (1 : Matrix n n ℂ) ⊗ₖ (CFC.log H)ᵀ)) =
      ((1 : Matrix n n ℂ) ⊗ₖ Hᵀ - A ⊗ₖ (1 : Matrix n n ℂ)) +
        ((A * CFC.log A) ⊗ₖ (1 : Matrix n n ℂ) -
          A ⊗ₖ (CFC.log H)ᵀ) := by
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_neg,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, posDef_mul_inv_self hA]
    simp only [Matrix.one_mul, Matrix.mul_one]
    abel
  rw [hX, phiMap_add, phiMap_sub, phiMap_sub, phiMap_kronecker,
    phiMap_kronecker, phiMap_kronecker, phiMap_kronecker]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  rw [← Matrix.transpose_mul, Matrix.trace_transpose,
    Matrix.trace_transpose, Matrix.trace_transpose,
    Matrix.trace_transpose, Matrix.trace_mul_comm (CFC.log H) A,
    Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub]
  ring

end PhiPsi

/-! ## The main theorem (8.1.4) -/

section MREConvexMain

/-- **Book Theorem 8.1.4, §8.8 assembly**  "the matrix relative
entropy is a convex function": for pd `Aᵢ`, `Hᵢ` and `τ ∈ [0,1]`,
`D(τA₁ + τ̄A₂; τH₁ + τ̄H₂) ≤ τ·D(A₁; H₁) + τ̄·D(A₂; H₂)` — via the
operator convexity of the matrix perspective evaluated at the commuting
Kronecker pairs (with the SI-C8-1 transpose repair) and the
order-preserving functional `φ`.

Author note: the proof uses the transpose repair to the book’s `φ` computation; the resulting convexity statement itself is unchanged. -/
theorem mre_convex {A₁ A₂ H₁ H₂ : Matrix n n ℂ} (hA₁ : A₁.PosDef)
    (hA₂ : A₂.PosDef) (hH₁ : H₁.PosDef) (hH₂ : H₂.PosDef) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    mre (τ • A₁ + (1 - τ) • A₂) (τ • H₁ + (1 - τ) • H₂) ≤
      τ * mre A₁ H₁ + (1 - τ) * mre A₂ H₂ := by
  have hAc : (τ • A₁ + (1 - τ) • A₂).PosDef :=
    posDef_convex_combo hA₁ hA₂ hτ
  have hHc : (τ • H₁ + (1 - τ) • H₂).PosDef :=
    posDef_convex_combo hH₁ hH₂ hτ
  -- the operator convexity of the perspective at the Kronecker pairs
  have hpersp := matrixPerspective_operator_convex
    (operatorConvexOn_entropyKernel ((n × n) ⊕ (n × n)))
    (posDef_kronecker hA₁ Matrix.PosDef.one)
    (posDef_kronecker hA₂ Matrix.PosDef.one)
    (posDef_kronecker Matrix.PosDef.one hH₁.transpose)
    (posDef_kronecker Matrix.PosDef.one hH₂.transpose) hτ
  -- convex combinations pass through `· ⊗ I` and `I ⊗ ·ᵀ`
  have hcombA : τ • (A₁ ⊗ₖ (1 : Matrix n n ℂ)) +
      (1 - τ) • (A₂ ⊗ₖ (1 : Matrix n n ℂ)) =
      (τ • A₁ + (1 - τ) • A₂) ⊗ₖ (1 : Matrix n n ℂ) := by
    rw [Matrix.add_kronecker, Matrix.smul_kronecker,
      Matrix.smul_kronecker]
  have hcombH : τ • ((1 : Matrix n n ℂ) ⊗ₖ H₁ᵀ) +
      (1 - τ) • ((1 : Matrix n n ℂ) ⊗ₖ H₂ᵀ) =
      (1 : Matrix n n ℂ) ⊗ₖ (τ • H₁ + (1 - τ) • H₂)ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_smul, Matrix.kronecker_add, Matrix.kronecker_smul,
      Matrix.kronecker_smul]
  rw [hcombA, hcombH] at hpersp
  -- apply the order-preserving functional φ and identify the traces
  have hphi := phiMap_loewner_mono hpersp
  rw [phiMap_add, phiMap_real_smul, phiMap_real_smul,
    phi_perspective_eq_mre_trace hAc hHc,
    phi_perspective_eq_mre_trace hA₁ hH₁,
    phi_perspective_eq_mre_trace hA₂ hH₂] at hphi
  -- take real parts
  have hre := (Complex.le_def.mp hphi).1
  simp only [Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul]
    at hre
  exact hre

end MREConvexMain

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# §8.1: Lieb's Theorem

* **Fact (Partial Maximization, 8.1.5)** 
  `partial_maximization` — "partial maximization of a concave function
  produces a concave function", with the book's `ε`-argument; the book's
  implicit hypothesis that the suprema exist is rendered by a `BddAbove`
  assumption.
* **Lemma (Variational Formula for Trace, 8.1.6)** 
  `trace_variational_isGreatest`, in `IsGreatest` form (the supremum is
  finite and attained at `T = M`, exactly as in the book's proof).
* **Display (8.1.2)**  `trace_exp_isGreatest_mre` — the trace
  exponential as the (attained) supremum of
  `tr(TH) + tr A − D(T; A)` over pd `T`.
* **Theorem (Lieb, 8.1.1 = Theorem 3.4.1)**  `lieb_theorem` —
  for fixed Hermitian `H`, `A ↦ tr exp(H + log A)` is concave on the pd
  cone. Assembled without suprema: the
  equality case `trace_exp_eq_at_optimizer` at `Tᵢ = exp(H + log Aᵢ)`,
  the upper bound from (8.1.2) at the mixed
  `T = τT₁ + τ̄T₂`, and the convexity of the matrix relative entropy
  (`mre_convex`).  This is the mathematical content of the book's
  partial-maximization step, with the near-optimizers replaced by exact
  ones.

The chapter-level theorem `lieb_trace_exp_log_concave` (Theorem 3.4.1) is derived from `lieb_theorem`.
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A H M T Hm : Matrix n n ℂ}

/-! ## Partial maximization (Fact 8.1.5) -/

section PartialMax

/-- **Book Fact (Partial Maximization, 8.1.5)**  "Let `f` be a
concave function of two variables.  Then the function
`y ↦ sup_x f(x; y)` obtained by partial maximization is concave" — the
book's `ε`-argument.  The book implicitly assumes the suprema are finite
(`hbdd`) and the domains are convex and nonempty.

Author note: Lean makes explicit the book’s hidden nonemptiness, convexity, and finite-supremum hypotheses. -/
theorem partial_maximization {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {s : Set E} {t : Set F}
    (hs : Convex ℝ s) (ht : Convex ℝ t) (hne : s.Nonempty)
    (f : E × F → ℝ) (hf : ConcaveOn ℝ (s ×ˢ t) f)
    (hbdd : ∀ y ∈ t, BddAbove ((fun x => f (x, y)) '' s)) :
    ConcaveOn ℝ t (fun y => sSup ((fun x => f (x, y)) '' s)) := by
  refine ⟨ht, fun y₁ hy₁ y₂ hy₂ a b ha hb hab => ?_⟩
  -- goal: a • sSup(…y₁) + b • sSup(…y₂) ≤ sSup(…(a•y₁+b•y₂))
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- the book's near-optimizers x₁ and x₂
  have hne₁ : ((fun x => f (x, y₁)) '' s).Nonempty := hne.image _
  have hne₂ : ((fun x => f (x, y₂)) '' s).Nonempty := hne.image _
  obtain ⟨v₁, hv₁mem, hv₁⟩ := exists_lt_of_lt_csSup hne₁
    (show sSup ((fun x => f (x, y₁)) '' s) - ε / 2 <
      sSup ((fun x => f (x, y₁)) '' s) by linarith)
  obtain ⟨v₂, hv₂mem, hv₂⟩ := exists_lt_of_lt_csSup hne₂
    (show sSup ((fun x => f (x, y₂)) '' s) - ε / 2 <
      sSup ((fun x => f (x, y₂)) '' s) by linarith)
  obtain ⟨x₁, hx₁, rfl⟩ := hv₁mem
  obtain ⟨x₂, hx₂, rfl⟩ := hv₂mem
  -- the concavity step of the book's display
  have hcc := hf.2 (Set.mk_mem_prod hx₁ hy₁) (Set.mk_mem_prod hx₂ hy₂)
    ha hb hab
  have hpt : a • ((x₁, y₁) : E × F) + b • (x₂, y₂) =
      (a • x₁ + b • x₂, a • y₁ + b • y₂) := by
    simp
  rw [hpt] at hcc
  -- the mixed point is feasible for the partial supremum
  have hxs : a • x₁ + b • x₂ ∈ s := hs hx₁ hx₂ ha hb hab
  have hup : f (a • x₁ + b • x₂, a • y₁ + b • y₂) ≤
      sSup ((fun x => f (x, a • y₁ + b • y₂)) '' s) :=
    le_csSup (hbdd _ (ht hy₁ hy₂ ha hb hab)) ⟨_, hxs, rfl⟩
  -- combine, absorbing the ε-loss
  have ha2 : a ≤ 1 := by linarith
  have hb2 : b ≤ 1 := by linarith
  have h1 : a * (ε / 2) ≤ ε / 2 := by nlinarith
  have h2 : b * (ε / 2) ≤ ε / 2 := by nlinarith
  simp only [smul_eq_mul] at hcc ⊢
  nlinarith [hcc, hup, hv₁, hv₂]

end PartialMax

/-! ## The variational formula for the trace (Lemma 8.1.6) -/

section Variational

/-- **Book Lemma (Variational Formula for Trace, 8.1.6)**  "Let `M`
be a positive-definite matrix.  Then
`tr M = sup_{T ≻ 0} tr[T log M − T log T + T]`" — rendered in
`IsGreatest` form: `tr M` is an upper bound of the bracket over pd `T`,
attained at `T = M` (exactly the content of the book's proof, which
rearranges `D(T; M) ≥ 0` and notes equality at `T = M`).

Author note: Lean records attainment and the upper-bound property as `IsGreatest`, stronger data than the displayed supremum equality. -/
theorem trace_variational_isGreatest (hM : M.PosDef) :
    IsGreatest ((fun T : Matrix n n ℂ =>
        ((T * CFC.log M - T * CFC.log T + T).trace).re) ''
      {T : Matrix n n ℂ | T.PosDef}) ((M.trace).re) := by
  constructor
  · -- attained at `T = M`
    refine ⟨M, hM, ?_⟩
    show ((M * CFC.log M - M * CFC.log M + M).trace).re = (M.trace).re
    rw [sub_self, zero_add]
  · -- upper bound: rearranged nonnegativity of `D(T; M)`
    rintro v ⟨T, hT, rfl⟩
    have h0 := mre_nonneg hT hM
    have hid : T * (CFC.log T - CFC.log M) - (T - M) =
        -(T * CFC.log M - T * CFC.log T + T) + M := by
      noncomm_ring
    rw [mre, hid, Matrix.trace_add, Matrix.trace_neg] at h0
    simp only [Complex.add_re, Complex.neg_re] at h0
    linarith

/-- **Book equation (8.1.2)**  "`tr exp(H + log A) =
sup_{T ≻ 0} [tr(TH) + tr A − D(T; A)]`" — in `IsGreatest` form.  Obtained
from 8.1.6 at `M = exp(H + log A)`, using `log exp = id` on
Hermitian matrices and the definition of the matrix relative entropy.

Author note: Lean records the variational identity in the stronger `IsGreatest` form. -/
theorem trace_exp_isGreatest_mre (hHm : Hm.IsHermitian) (hA : A.PosDef) :
    IsGreatest ((fun T : Matrix n n ℂ =>
        ((T * Hm).trace).re + (A.trace).re - mre T A) ''
      {T : Matrix n n ℂ | T.PosDef})
      (((NormedSpace.exp (Hm + CFC.log A)).trace).re) := by
  have hMpd : (NormedSpace.exp (Hm + CFC.log A)).PosDef :=
    posDef_exp (hHm.add (isHermitian_cfc _ _))
  have hbase := trace_variational_isGreatest hMpd
  have hlog : CFC.log (NormedSpace.exp (Hm + CFC.log A)) =
      Hm + CFC.log A := log_exp_eq (hHm.add (isHermitian_cfc _ _))
  have hcongr : ∀ T ∈ {T : Matrix n n ℂ | T.PosDef},
      ((T * CFC.log (NormedSpace.exp (Hm + CFC.log A)) -
        T * CFC.log T + T).trace).re =
      ((T * Hm).trace).re + (A.trace).re - mre T A := by
    intro T _
    rw [hlog, mre]
    have hid : T * (Hm + CFC.log A) - T * CFC.log T + T =
        T * Hm + A - (T * (CFC.log T - CFC.log A) - (T - A)) := by
      noncomm_ring
    rw [hid, Matrix.trace_sub, Matrix.trace_add]
    simp only [Complex.sub_re, Complex.add_re]
  rw [← Set.image_congr hcongr]
  exact hbase

/-- **Book equality case (proof of 8.1.6 / 8.1.1)** 
at the optimizer `T = exp(H + log A)` the bracket of (8.1.2)
*equals* the trace exponential. -/
lemma trace_exp_eq_at_optimizer (hHm : Hm.IsHermitian) (_hA : A.PosDef) :
    ((NormedSpace.exp (Hm + CFC.log A)).trace).re =
      (((NormedSpace.exp (Hm + CFC.log A)) * Hm).trace).re +
        (A.trace).re - mre (NormedSpace.exp (Hm + CFC.log A)) A := by
  have hlogT : CFC.log (NormedSpace.exp (Hm + CFC.log A)) =
      Hm + CFC.log A := log_exp_eq (hHm.add (isHermitian_cfc _ _))
  have hid : (NormedSpace.exp (Hm + CFC.log A)) *
      (CFC.log (NormedSpace.exp (Hm + CFC.log A)) - CFC.log A) -
      ((NormedSpace.exp (Hm + CFC.log A)) - A) =
      (NormedSpace.exp (Hm + CFC.log A)) * Hm -
        (NormedSpace.exp (Hm + CFC.log A)) + A := by
    rw [hlogT]
    noncomm_ring
  rw [mre, hid, Matrix.trace_add, Matrix.trace_sub]
  simp only [Complex.add_re, Complex.sub_re]
  ring

end Variational

/-! ## Lieb's theorem (Theorem 8.1.1) -/

section LiebMain

/-- **Book Theorem 8.1.1 (Lieb); equivalently Theorem 3.4.1.** Let
`H` be a fixed Hermitian matrix.  The map `A ↦ tr exp(H + log A)` is
concave on the convex cone of positive-definite Hermitian matrices."

Sup-free assembly: with
`Tᵢ := exp(H + log Aᵢ)`, the value at `Aᵢ` *equals* the
(8.1.2) bracket at `Tᵢ` (`trace_exp_eq_at_optimizer`); the value
at the convex combination dominates the bracket at `τT₁ + τ̄T₂`
(`trace_exp_isGreatest_mre`); and the brackets compare by the joint convexity
of the matrix relative entropy (`mre_convex`) at the generally distinct
optimizers `T₁` and `T₂`. -/
theorem lieb_theorem (Hm : Matrix n n ℂ) (hHm : Hm.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef}
      (fun A => ((NormedSpace.exp (Hm + CFC.log A)).trace).re) := by
  constructor
  · -- the pd matrices form a convex set
    intro A hA B hB a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    exact posDef_convex_combo hA hB ⟨ha, by linarith⟩
  intro A₁ hA₁ A₂ hA₂ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have ha1 : a ≤ 1 := by linarith
  have hT₁pd : (NormedSpace.exp (Hm + CFC.log A₁)).PosDef :=
    posDef_exp (hHm.add (isHermitian_cfc _ _))
  have hT₂pd : (NormedSpace.exp (Hm + CFC.log A₂)).PosDef :=
    posDef_exp (hHm.add (isHermitian_cfc _ _))
  have hAc : (a • A₁ + (1 - a) • A₂).PosDef :=
    posDef_convex_combo hA₁ hA₂ ⟨ha, ha1⟩
  have hTc : (a • NormedSpace.exp (Hm + CFC.log A₁) +
      (1 - a) • NormedSpace.exp (Hm + CFC.log A₂)).PosDef :=
    posDef_convex_combo hT₁pd hT₂pd ⟨ha, ha1⟩
  -- the upper bound of (8.1.2) at the mixed `T`
  have hub := (trace_exp_isGreatest_mre hHm hAc).2
    ⟨a • NormedSpace.exp (Hm + CFC.log A₁) +
      (1 - a) • NormedSpace.exp (Hm + CFC.log A₂), hTc, rfl⟩
  -- convexity of the matrix relative entropy at equal first arguments
  have hmre := mre_convex hT₁pd hT₂pd hA₁ hA₂ (τ := a) ⟨ha, ha1⟩
  -- the equality cases at the exact optimizers
  have he₁ := trace_exp_eq_at_optimizer hHm hA₁
  have he₂ := trace_exp_eq_at_optimizer hHm hA₂
  -- linear expansions of the traces
  have hlin1 : (((a • NormedSpace.exp (Hm + CFC.log A₁) +
      (1 - a) • NormedSpace.exp (Hm + CFC.log A₂)) * Hm).trace).re =
      a * (((NormedSpace.exp (Hm + CFC.log A₁)) * Hm).trace).re +
        (1 - a) * (((NormedSpace.exp (Hm + CFC.log A₂)) * Hm).trace).re := by
    rw [Matrix.add_mul, Matrix.trace_add, smul_mul_assoc, smul_mul_assoc,
      Matrix.trace_smul, Matrix.trace_smul]
    simp [Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul]
  have hlin2 : (((a • A₁ + (1 - a) • A₂) : Matrix n n ℂ).trace).re =
      a * (A₁.trace).re + (1 - a) * (A₂.trace).re := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
    simp [Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul]
  show a • ((NormedSpace.exp (Hm + CFC.log A₁)).trace).re +
      (1 - a) • ((NormedSpace.exp (Hm + CFC.log A₂)).trace).re ≤
      ((NormedSpace.exp (Hm + CFC.log (a • A₁ + (1 - a) • A₂))).trace).re
  simp only [smul_eq_mul]
  rw [he₁, he₂]
  simp only [] at hub
  rw [hlin1, hlin2] at hub
  linarith [hub, hmre]

end LiebMain

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# §8.3.1–§8.3.3: Trace Functions and Monotonicity

* **Definition (Trace function)**  the book defines
  `tr f(A) = Σᵢ f(λᵢ(A))` over the decreasingly ordered eigenvalues and
  notes "this formula gives the same result as composing the trace with
  the standard matrix function `f`" — rendered by `sortedEig` (the `i`-th
  largest eigenvalue, via `Tuple.sort` and index reversal) and
  `traceFn_eq_sum_sorted` (with the unsorted correspondence
  `trace_cfc_eq_sum` from the Prelude).
* **§8.3.3 "Eigenvalue Decompositions, Redux"**  `spectral_sum_outer` —
  `A = Σᵢ λᵢ uᵢuᵢ*` (the display; the sorted enumeration is `sortedEig`).
* **Fact (Semidefinite Order implies Eigenvalue Order,
  8.3.2)**  `sdp_eig_order`.  The book cites the
  Courant–Fischer theorem (not in Mathlib); the proof here recovers the
  one-sided minimax argument it compresses: for the `i`-th sorted pair,
  the span of the top `i+1` eigenvectors of `A` and the span of the
  bottom `d − i` eigenvectors of `H` intersect nontrivially by dimension
  counting (`finrank_sup_add_finrank_inf_eq`), and the Rayleigh quotient
  of a witness vector is squeezed between the two sorted eigenvalues.
* **Proposition (Monotone Trace Functions, 8.3.3)** 
  `trace_monotone_of_monotoneOn`.
* **Example (Trace Exponential is Monotone)** 
  `trace_exp_monotone_of_loewner` (derived, as in the book, from the
  proposition; `trace_exp_monotone` in the Chapter 2 module proves the same
  statement by the Peierls–Bogoliubov route).

The remaining §8.3 items (Generalized Klein inequality, the Klein
inequality, and nonnegativity of the matrix relative entropy) appear
earlier in this module.
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A H : Matrix n n ℂ}

/-! ## Sorted eigenvalues ("the `i`-th largest eigenvalue") -/

section SortedEig

/-- Lean implementation helper: the index bijection that enumerates the
eigenvalues of a Hermitian matrix in weakly decreasing order
(`Tuple.sort` composed with index reversal). -/
noncomputable def sortIdx (hA : A.IsHermitian) :
    Fin (Fintype.card n) ≃ n :=
  ((Fin.revPerm).trans
    (Tuple.sort (hA.eigenvalues ∘ (Fintype.equivFin n).symm))).trans
    (Fintype.equivFin n).symm

/-- **Book §8.3.1 (ordered-eigenvalue notation).** The notation `λᵢ(A)`
denotes the `i`-th largest eigenvalue of `A`. -/
noncomputable def sortedEig (hA : A.IsHermitian) :
    Fin (Fintype.card n) → ℝ :=
  hA.eigenvalues ∘ (sortIdx hA)

/-- Lean implementation helper: the sorted eigenvalues are weakly
decreasing (the book's `λ₁ ≥ … ≥ λ_d`). -/
lemma sortedEig_antitone (hA : A.IsHermitian) : Antitone (sortedEig hA) := by
  intro i j hij
  have h1 : Monotone ((hA.eigenvalues ∘ (Fintype.equivFin n).symm) ∘
      Tuple.sort (hA.eigenvalues ∘ (Fintype.equivFin n).symm)) :=
    Tuple.monotone_sort _
  have h2 : Fin.rev j ≤ Fin.rev i := Fin.rev_le_rev.mpr hij
  exact h1 h2

/-- **Book §8.3.1 (definition of a trace function).** The identity
`tr f(A) = Σᵢ f(λᵢ(A))` […]
This formula gives the same result as composing the trace with the
standard matrix function `f`. -/
theorem traceFn_eq_sum_sorted (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ((cfc f A).trace).re = ∑ i, f (sortedEig hA i) := by
  rw [trace_cfc_eq_sum hA f, Complex.ofReal_re,
    ← Equiv.sum_comp (sortIdx hA) (fun j => f (hA.eigenvalues j))]
  rfl

/-- **Book §8.3.3 (Eigenvalue Decompositions, Redux)**  "each Hermitian matrix
`A` can be expressed as `A = Σᵢ λᵢ uᵢuᵢ*`" with orthonormal
eigenvectors. -/
theorem spectral_sum_outer (hA : A.IsHermitian) :
    A = ∑ j, ((hA.eigenvalues j : ℝ) : ℂ) •
      Matrix.vecMulVec (⇑(hA.eigenvectorBasis j))
        (star ⇑(hA.eigenvectorBasis j)) := by
  have hsa : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  have h1 := cfc_eq_sum_outer hA (id : ℝ → ℝ)
  rwa [cfc_id ℝ A] at h1

end SortedEig

/-! ## Rayleigh bounds on spans of eigenvector subfamilies -/

section RayleighSpans

/-- Lean implementation helper: a vector in the span of an orthonormal
subfamily is orthogonal to the other basis vectors. -/
lemma coeff_eq_zero_of_mem_span_subfamily
    {b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)} {s : Set n}
    {w : EuclideanSpace ℂ n} (hw : w ∈ Submodule.span ℂ (⇑b '' s))
    {j : n} (hj : j ∉ s) : (inner ℂ (b j) w : ℂ) = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    have h1 := orthonormal_iff_ite.mp b.orthonormal j k
    rw [h1, if_neg (fun h : j = k => hj (h ▸ hk))]
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]

/-- Lean implementation helper: the entries of `Vᴴ u` are the overlaps
with the eigenvector basis. -/
private lemma conjTranspose_mulVec_entry (hA : A.IsHermitian)
    (u : n → ℂ) (j : n) :
    ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ u) j =
      star (⇑(hA.eigenvectorBasis j) : n → ℂ) ⬝ᵥ u := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    Pi.star_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hA.eigenvectorUnitary_apply]

/-- Lean implementation helper (`u†Au ≥ λᵢ u†u` on the top span): the
Rayleigh quotient on the span of the eigenvectors with the `i+1` largest
eigenvalues is at least `λᵢ(A)`. -/
lemma rayleigh_ge_of_mem_span_top (hA : A.IsHermitian)
    (i : Fin (Fintype.card n)) {w : EuclideanSpace ℂ n}
    (hw : w ∈ Submodule.span ℂ (⇑(hA.eigenvectorBasis) ''
      ↑(Finset.image (sortIdx hA) (Finset.Iic i)))) :
    sortedEig hA i * l2norm (⇑w) ^ 2 ≤ rayleigh A (⇑w) := by
  rw [rayleigh_eq_sum hA,
    ← sum_norm_sq_conjTranspose_mulVec hA.eigenvectorUnitary.2 (⇑w),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j ∈ Finset.image (sortIdx hA) (Finset.Iic i)
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have h1 : sortedEig hA i ≤ hA.eigenvalues (sortIdx hA k) :=
      sortedEig_antitone hA (Finset.mem_Iic.mp hk)
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · have h2 : ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ ⇑w) j = 0 := by
      rw [conjTranspose_mulVec_entry hA, ← inner_eq_star_dotProduct]
      exact coeff_eq_zero_of_mem_span_subfamily hw
        (fun h => hj (Finset.mem_coe.mp h))
    rw [h2]
    simp

/-- Lean implementation helper (`u†Hu ≤ λᵢ u†u` on the bottom span): the
Rayleigh quotient on the span of the eigenvectors with the `d − i`
smallest eigenvalues is at most `λᵢ(H)`. -/
lemma rayleigh_le_of_mem_span_bot (hH : H.IsHermitian)
    (i : Fin (Fintype.card n)) {w : EuclideanSpace ℂ n}
    (hw : w ∈ Submodule.span ℂ (⇑(hH.eigenvectorBasis) ''
      ↑(Finset.image (sortIdx hH) (Finset.Ici i)))) :
    rayleigh H (⇑w) ≤ sortedEig hH i * l2norm (⇑w) ^ 2 := by
  rw [rayleigh_eq_sum hH,
    ← sum_norm_sq_conjTranspose_mulVec hH.eigenvectorUnitary.2 (⇑w),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j ∈ Finset.image (sortIdx hH) (Finset.Ici i)
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have h1 : hH.eigenvalues (sortIdx hH k) ≤ sortedEig hH i :=
      sortedEig_antitone hH (Finset.mem_Ici.mp hk)
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · have h2 : ((hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ ⇑w) j = 0 := by
      rw [conjTranspose_mulVec_entry hH, ← inner_eq_star_dotProduct]
      exact coeff_eq_zero_of_mem_span_subfamily hw
        (fun h => hj (Finset.mem_coe.mp h))
    rw [h2]
    simp

/-- Lean implementation helper: the span of an orthonormal subfamily has
dimension equal to the size of the subfamily. -/
lemma finrank_span_orthonormal_finset {ι : Type*} [Fintype ι]
    [DecidableEq ι] {v : ι → EuclideanSpace ℂ n} (hv : Orthonormal ℂ v)
    (s : Finset ι) :
    Module.finrank ℂ ↥(Submodule.span ℂ (v '' ↑s)) = s.card := by
  rw [Set.image_eq_range]
  have hli := (hv.comp (Subtype.val : ↥(↑s : Set ι) → ι)
    Subtype.val_injective).linearIndependent
  rw [show (Set.range fun x : ↥(↑s : Set ι) => v ↑x) =
    Set.range (v ∘ Subtype.val) from rfl, finrank_span_eq_card hli]
  simp

end RayleighSpans

/-! ## Semidefinite order implies eigenvalue order (Fact
8.3.2) -/

section EigOrder

/-- **Book Fact (Semidefinite Order implies Eigenvalue Order,
8.3.2)**  "For Hermitian matrices `A` and `H`, `A ≼ H`
implies `λᵢ(A) ≤ λᵢ(H)` for each index `i`" — recovered one-sided
Courant–Fischer proof (dimension counting plus the two Rayleigh
bounds). -/
theorem sdp_eig_order (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hle : A ≤ H) (i : Fin (Fintype.card n)) :
    sortedEig hA i ≤ sortedEig hH i := by
  classical
  set S := Submodule.span ℂ (⇑(hA.eigenvectorBasis) ''
    ↑(Finset.image (sortIdx hA) (Finset.Iic i))) with hS
  set T := Submodule.span ℂ (⇑(hH.eigenvectorBasis) ''
    ↑(Finset.image (sortIdx hH) (Finset.Ici i))) with hT
  have hdS : Module.finrank ℂ ↥S = (i : ℕ) + 1 := by
    rw [hS, finrank_span_orthonormal_finset hA.eigenvectorBasis.orthonormal,
      Finset.card_image_of_injective _ (sortIdx hA).injective, Fin.card_Iic]
  have hdT : Module.finrank ℂ ↥T = Fintype.card n - (i : ℕ) := by
    rw [hT, finrank_span_orthonormal_finset hH.eigenvectorBasis.orthonormal,
      Finset.card_image_of_injective _ (sortIdx hH).injective, Fin.card_Ici]
  -- the two spans intersect nontrivially
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq S T
  have hamb : Module.finrank ℂ ↥(S ⊔ T) ≤ Fintype.card n := by
    have h1 := Submodule.finrank_le (S ⊔ T)
    rwa [finrank_euclideanSpace] at h1
  have hpos : 0 < Module.finrank ℂ ↥(S ⊓ T) := by
    have hi : (i : ℕ) < Fintype.card n := i.isLt
    omega
  haveI : Nontrivial ↥(S ⊓ T) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨⟨w, hwST⟩, hw0⟩ := exists_ne (0 : ↥(S ⊓ T))
  have hwmem := Submodule.mem_inf.mp hwST
  have hwne : w ≠ 0 := by
    intro h
    exact hw0 (Subtype.ext h)
  -- the Rayleigh squeeze
  have hb1 := rayleigh_ge_of_mem_span_top hA i hwmem.1
  have hb2 := rayleigh_mono_of_loewner_le hle (⇑w)
  have hb3 := rayleigh_le_of_mem_span_bot hH i hwmem.2
  have hchain := le_trans hb1 (le_trans hb2 hb3)
  -- the witness has positive norm
  have hnpos : 0 < l2norm (⇑w) ^ 2 := by
    rcases (l2norm_nonneg (⇑w)).lt_or_eq with h | h
    · positivity
    · exfalso
      apply hwne
      have h1 : ∑ p, ‖(⇑w : n → ℂ) p‖ ^ 2 = 0 := by
        rw [← l2norm_sq, ← h]
        norm_num
      have h2 : ∀ p, (⇑w : n → ℂ) p = 0 := by
        intro p
        have h3 := (Finset.sum_eq_zero_iff_of_nonneg
          (fun q _ => by positivity)).mp h1 p (Finset.mem_univ p)
        simpa using h3
      ext p
      exact h2 p
  exact le_of_mul_le_mul_right (by
    calc sortedEig hA i * l2norm (⇑w) ^ 2 ≤ rayleigh A (⇑w) := hb1
      _ ≤ rayleigh H (⇑w) := hb2
      _ ≤ sortedEig hH i * l2norm (⇑w) ^ 2 := hb3) hnpos

end EigOrder

/-! ## Monotone trace functions (Proposition 8.3.3) -/

section MonotoneTraceMain

/-- **Book Proposition (Monotone Trace Functions, 8.3.3)** 
"Let `f : I → ℝ` be a weakly increasing function on an interval `I`, and
let `A` and `H` be Hermitian matrices whose eigenvalues are contained in
`I`.  Then `A ≼ H` implies `tr f(A) ≤ tr f(H)`." -/
theorem trace_monotone_of_monotoneOn {f : ℝ → ℝ} {I : Set ℝ}
    (hf : MonotoneOn f I) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hAI : ∀ i, hA.eigenvalues i ∈ I) (hHI : ∀ i, hH.eigenvalues i ∈ I)
    (hle : A ≤ H) :
    ((cfc f A).trace).re ≤ ((cfc f H).trace).re := by
  rw [traceFn_eq_sum_sorted hA f, traceFn_eq_sum_sorted hH f]
  refine Finset.sum_le_sum fun i _ => ?_
  exact hf (hAI _) (hHI _) (sdp_eig_order hA hH hle i)

/-- **Book Proposition 8.3.3 (trace-exponential example).** The implication `A ≼ H` gives
`tr e^A ≤ tr e^H` for all Hermitian matrices `A` and `H`. This is the
special case used by the matrix-concentration argument (also proved by the
Peierls–Bogoliubov route in the Chapter 2 module). -/
theorem trace_exp_monotone_of_loewner (hA : A.IsHermitian)
    (hH : H.IsHermitian) (hle : A ≤ H) :
    ((NormedSpace.exp A).trace).re ≤ ((NormedSpace.exp H).trace).re := by
  rw [matrixExp_eq_cfc hA, matrixExp_eq_cfc hH]
  exact trace_monotone_of_monotoneOn
    (fun a _ b _ hab => Real.exp_le_exp.mpr hab) hA hH
    (fun i => Set.mem_univ _) (fun i => Set.mem_univ _) hle

end MonotoneTraceMain

end MatrixConcentration
