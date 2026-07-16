import MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices
import MatrixConcentration.Chapter3_MatrixLaplaceTransformMethod
import MatrixConcentration.Chapter5_SumOfPSDMatrices
import MatrixConcentration.Chapter6_SumOfBoundedRandomMatrices
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Chapter 7: Intrinsic dimension

This consolidated chapter contains:

* **Book §7.1:** intrinsic dimension and its spectral properties;
* **Book §7.4:** generalized matrix Laplace-transform bounds;
* **Book §7.5:** the intrinsic-dimension trace lemma;
* **Book §7.2:** intrinsic Chernoff and column-submatrix estimates;
* **Book §7.3 and §7.7:** intrinsic Bernstein tail and expectation bounds;
* **Book §7.3.3:** sampling and randomized-multiplication applications.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The intrinsic dimension of a matrix (Tropp §7.1, §7.3.1)

**Definition 7.1.1**: for a positive-semidefinite matrix `A`, the intrinsic
dimension is `intdim(A) = tr A / ‖A‖` (`intdim`; Lean's `0/0 = 0` convention
gives `intdim 0 = 0` — the book implicitly assumes `A ≠ 0`).

§7.1 facts:

* the display `1 ≤ intdim(A) ≤ rank(A) ≤ dim(A)` (`one_le_intdim`,
  `intdim_le_rank`; the last inequality is Mathlib's `Matrix.rank_le_card`);
* "The first inequality is attained precisely when `A` has rank one"
  (`intdim_eq_one_iff_rank_eq_one`);
* "the second inequality is attained precisely when `A` is a multiple of the
  identity" — as literally stated for `intdim ≤ rank`, this is refuted by
  `intdim_eq_rank_attained_without_identity`:
  `diag(1,0)` attains `intdim = rank` and is not a multiple of the identity).
  The correct reading — attainment of the composite inequality
  `intdim ≤ dim` — is `intdim_eq_card_iff` (with `intdim_smul_one`);
* 0-homogeneity (`intdim_smul`);
* non-monotonicity with respect to the semidefinite order
  (`intdim_not_monotone` — "we can drive the intrinsic dimension to one by
  increasing one eigenvalue of `A` substantially").

§7.3.1 facts about the block-diagonal intrinsic dimension (7.3.1's
`d = intdim(diag(V₁,V₂))`):

* the display `d = (tr V₁ + tr V₂)/max{‖V₁‖, ‖V₂‖}` (`intdim_fromBlocks_eq`);
* the intrinsic-dimension bounds of §7.3.1:
  `min{intdim V₁, intdim V₂} ≤ d ≤ intdim V₁ + intdim V₂`
  (`min_intdim_le_intdim_fromBlocks`, `intdim_fromBlocks_le_add`);
* "This intrinsic dimension quantity never exceeds the total of the two side
  lengths" (`intdim_fromBlocks_le_card`).

§7.2.2 identity `intdim(BB*) = srank(B)` (`intdim_gram_eq_stableRank`, plus
the `B*B` variant used by the §7.3.3 application).
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {A : Matrix n n ℂ}

section Definition

/-- **Book Definition 7.1.1**: the intrinsic dimension
`intdim(A) = tr A / ‖A‖` of a positive-semidefinite matrix `A`.

**Author note.** Lean totalizes the quotient at the zero matrix, so
`intdim 0 = 0`; the Book's subsequent lower bounds require `A ≠ 0`. -/
noncomputable def intdim (A : Matrix n n ℂ) : ℝ := (A.trace).re / ‖A‖

/-- Lean implementation helper: `intdim 0 = 0` (Lean `0/0` convention). -/
lemma intdim_zero : intdim (0 : Matrix n n ℂ) = 0 := by
  rw [intdim, Matrix.trace_zero]
  simp

/-- Lean implementation helper: the intrinsic dimension of a psd matrix is
nonnegative. -/
lemma intdim_nonneg (hA : A.PosSemidef) : 0 ≤ intdim A := by
  refine div_nonneg ?_ (norm_nonneg A)
  rw [trace_re_eq_sum_eigenvalues hA.1]
  exact Finset.sum_nonneg fun i _ => hA.eigenvalues_nonneg i

/-- **Book §7.1** (C7-05): "The intrinsic dimension is 0-homogeneous, so it
is insensitive to changes in the scale of the matrix `A`."  Implicit source
claim.

**Author note.** The Book discusses positive-semidefinite matrices, while this
algebraic scaling identity holds for every complex matrix. -/
lemma intdim_smul {c : ℝ} (hc : 0 < c) (A : Matrix n n ℂ) :
    intdim (c • A) = intdim A := by
  rw [intdim, intdim, Matrix.trace_smul, norm_smul, Complex.smul_re,
    Real.norm_eq_abs, abs_of_pos hc]
  exact mul_div_mul_left _ _ hc.ne'

end Definition

section Chain

variable [Nonempty n]

/-- **Book §7.1 display, first inequality** (C7-02): `1 ≤ intdim(A)` for a
nonzero psd matrix.  (The nondegeneracy `A ≠ 0` is implicit in the source:
`intdim 0` is a `0/0`.)  Explicit (unnumbered) source display. -/
theorem one_le_intdim (hA : A.PosSemidef) (h0 : A ≠ 0) : 1 ≤ intdim A := by
  have hnorm : 0 < ‖A‖ := norm_pos_iff.mpr h0
  rw [intdim, le_div_iff₀ hnorm, one_mul]
  calc ‖A‖ = lambdaMax hA.1 := posSemidef_l2_opNorm_eq_lambdaMax hA
    _ ≤ (A.trace).re := lambdaMax_le_trace_re_of_posSemidef hA

/-- **Book §7.1 display, second inequality** (C7-02): `intdim(A) ≤ rank(A)`
for a psd matrix (`tr A = Σ λ_i` runs over the `rank(A)` nonzero eigenvalues,
each at most `λ_max = ‖A‖`).  Explicit (unnumbered) source display; the third
inequality `rank(A) ≤ dim(A)` is Mathlib's `Matrix.rank_le_card`. -/
theorem intdim_le_rank (hA : A.PosSemidef) : intdim A ≤ (A.rank : ℝ) := by
  by_cases h0 : A = 0
  · rw [h0, intdim_zero]
    exact Nat.cast_nonneg _
  have hnorm : 0 < ‖A‖ := norm_pos_iff.mpr h0
  rw [intdim, div_le_iff₀ hnorm, trace_re_eq_sum_eigenvalues hA.1]
  have hfilter : ∑ i, hA.1.eigenvalues i =
      ∑ i ∈ Finset.univ.filter (fun i => hA.1.eigenvalues i ≠ 0),
        hA.1.eigenvalues i := by
    rw [Finset.sum_filter_of_ne]
    intro i _ hi
    exact hi
  rw [hfilter]
  have hcard : A.rank =
      (Finset.univ.filter (fun i => hA.1.eigenvalues i ≠ 0)).card := by
    rw [hA.1.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  calc (∑ i ∈ Finset.univ.filter (fun i => hA.1.eigenvalues i ≠ 0),
        hA.1.eigenvalues i)
      ≤ (Finset.univ.filter (fun i => hA.1.eigenvalues i ≠ 0)).card • ‖A‖ := by
        refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
        rw [posSemidef_l2_opNorm_eq_lambdaMax hA]
        exact eigenvalues_le_lambdaMax hA.1 i
    _ = (A.rank : ℝ) * ‖A‖ := by rw [nsmul_eq_mul, hcard]

/-- **Book §7.1** (C7-03): "The first inequality is attained precisely when
`A` has rank one."  Implicit source claim. -/
theorem intdim_eq_one_iff_rank_eq_one (hA : A.PosSemidef) (h0 : A ≠ 0) :
    intdim A = 1 ↔ A.rank = 1 := by
  have hnorm : 0 < ‖A‖ := norm_pos_iff.mpr h0
  have hnn : ∀ i, 0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg
  constructor
  · intro h1
    -- `tr A = ‖A‖ = λ_max`, so all eigenvalues except a maximizer vanish
    have htr : (A.trace).re = ‖A‖ := by
      rw [intdim, div_eq_one_iff_eq hnorm.ne'] at h1
      exact h1
    obtain ⟨i₀, hi₀⟩ := exists_eigenvalues_eq_lambdaMax hA.1
    have hmax : hA.1.eigenvalues i₀ = ‖A‖ := by
      rw [hi₀, posSemidef_l2_opNorm_eq_lambdaMax hA]
    have hsum : ∑ i, hA.1.eigenvalues i = ‖A‖ := by
      rw [← trace_re_eq_sum_eigenvalues hA.1, htr]
    have herase : ∑ i ∈ Finset.univ.erase i₀, hA.1.eigenvalues i = 0 := by
      have hins := Finset.add_sum_erase Finset.univ hA.1.eigenvalues
        (Finset.mem_univ i₀)
      rw [hsum, hmax] at hins
      linarith
    have hzero : ∀ i ∈ Finset.univ.erase i₀, hA.1.eigenvalues i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).mp herase
    rw [hA.1.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    have hset : Finset.univ.filter (fun i => hA.1.eigenvalues i ≠ 0) =
        {i₀} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hj
        by_contra hne
        exact hj (hzero j (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩))
      · rintro rfl
        rw [hmax]
        exact hnorm.ne'
    rw [hset, Finset.card_singleton]
  · intro hrank
    -- a single nonzero eigenvalue carries the trace and the norm
    have hcard : Fintype.card {i // hA.1.eigenvalues i ≠ 0} = 1 := by
      rw [← hA.1.rank_eq_card_non_zero_eigs, hrank]
    obtain ⟨⟨i₀, hi₀⟩, huniq⟩ := Fintype.card_eq_one_iff.mp hcard
    have hzero : ∀ j, j ≠ i₀ → hA.1.eigenvalues j = 0 := by
      intro j hj
      by_contra hjne
      exact hj (congrArg Subtype.val (huniq ⟨j, hjne⟩))
    have hpos : 0 < hA.1.eigenvalues i₀ := lt_of_le_of_ne (hnn i₀) (Ne.symm hi₀)
    have htr : (A.trace).re = hA.1.eigenvalues i₀ := by
      rw [trace_re_eq_sum_eigenvalues hA.1]
      exact Finset.sum_eq_single i₀ (fun j _ hj => hzero j hj)
        (fun h => absurd (Finset.mem_univ i₀) h)
    have hmax : lambdaMax hA.1 = hA.1.eigenvalues i₀ := by
      obtain ⟨j, hj⟩ := exists_eigenvalues_eq_lambdaMax hA.1
      rcases eq_or_ne j i₀ with rfl | hne
      · exact hj.symm
      · have h1 : lambdaMax hA.1 = 0 := by rw [← hj, hzero j hne]
        have h2 := eigenvalues_le_lambdaMax hA.1 i₀
        rw [h1] at h2
        linarith
    rw [intdim, htr, posSemidef_l2_opNorm_eq_lambdaMax hA, hmax,
      div_self hpos.ne']

end Chain

section Identity

variable [Nonempty n]

/-- Lean implementation helper: `intdim(1) = dim`. -/
lemma intdim_one : intdim (1 : Matrix n n ℂ) = (Fintype.card n : ℝ) := by
  rw [intdim, Matrix.trace_one, l2_opNorm_one, div_one]
  simp

/-- **Book §7.1** (C7-04, positive half): a positive multiple of the identity
attains `intdim(A) = dim(A)`.  Implicit source claim (the "precisely when"
direction of the attainment statement for the composite dimension bound). -/
lemma intdim_smul_one {c : ℝ} (hc : 0 < c) :
    intdim (c • (1 : Matrix n n ℂ)) = (Fintype.card n : ℝ) := by
  rw [intdim_smul hc, intdim_one]

/-- **Book §7.1** (C7-04): the composite inequality
`intdim(A) ≤ dim(A)` is attained precisely when `A` is a (positive) multiple
of the identity.

**Author note.** The Book attaches this characterization to
`intdim ≤ rank`, which is false as stated; Lean proves the valid composite
bound `intdim ≤ dim`. -/
theorem intdim_eq_card_iff (hA : A.PosSemidef) (h0 : A ≠ 0) :
    intdim A = (Fintype.card n : ℝ) ↔
      ∃ c : ℝ, 0 < c ∧ A = c • (1 : Matrix n n ℂ) := by
  constructor
  · intro h
    have hnorm : 0 < ‖A‖ := norm_pos_iff.mpr h0
    -- all eigenvalues equal `λ_max = ‖A‖`
    have htr : (A.trace).re = (Fintype.card n : ℝ) * ‖A‖ := by
      rw [intdim, div_eq_iff hnorm.ne'] at h
      exact h
    have hsum0 : ∑ i, (‖A‖ - hA.1.eigenvalues i) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← trace_re_eq_sum_eigenvalues hA.1, htr, sub_self]
    have heq : ∀ i, hA.1.eigenvalues i = ‖A‖ := by
      intro i
      have hnn : ∀ j ∈ Finset.univ, 0 ≤ ‖A‖ - hA.1.eigenvalues j := by
        intro j _
        rw [sub_nonneg, posSemidef_l2_opNorm_eq_lambdaMax hA]
        exact eigenvalues_le_lambdaMax hA.1 j
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 i
        (Finset.mem_univ i)
      linarith [this]
    refine ⟨‖A‖, hnorm, ?_⟩
    -- spectral decomposition with a constant diagonal
    have hdiag : Matrix.diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) =
        (‖A‖ : ℂ) • (1 : Matrix n n ℂ) := by
      have hfun : RCLike.ofReal ∘ hA.1.eigenvalues =
          fun _ : n => (‖A‖ : ℂ) := by
        funext i
        simp [Function.comp_apply, heq i]
      rw [hfun, ← Matrix.diagonal_one, ← Matrix.diagonal_smul]
      congr 1
      funext i
      simp
    have hUU : (hA.1.eigenvectorUnitary : Matrix n n ℂ) *
        (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 := by
      rw [← star_eq_conjTranspose]
      exact Unitary.coe_mul_star_self _
    calc A = (hA.1.eigenvectorUnitary : Matrix n n ℂ) *
          Matrix.diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) *
          (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ := spectral_decomposition hA.1
      _ = (hA.1.eigenvectorUnitary : Matrix n n ℂ) * ((‖A‖ : ℂ) • 1) *
          (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by rw [hdiag]
      _ = (‖A‖ : ℂ) • ((hA.1.eigenvectorUnitary : Matrix n n ℂ) *
          (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ) := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = (‖A‖ : ℂ) • (1 : Matrix n n ℂ) := by rw [hUU]
      _ = ‖A‖ • (1 : Matrix n n ℂ) := (real_smul_eq_complex_smul _ _).symm
  · rintro ⟨c, hc, rfl⟩
    exact intdim_smul_one hc

end Identity

section Counterexamples

/-- Lean implementation helper: the psd matrix
`diag(1,0)` attains `intdim(A) = rank(A) = 1` and is not a multiple of the
identity.

**Author note.** This refutes the Book's literal equality characterization
for `intdim ≤ rank`; `intdim_eq_card_iff` gives the valid dimension version. -/
theorem intdim_eq_rank_attained_without_identity :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.PosSemidef ∧ A ≠ 0 ∧
      intdim A = (A.rank : ℝ) ∧ ∀ c : ℝ, A ≠ c • 1 := by
  set v : Fin 2 → ℝ := ![1, 0] with hv
  set A₀ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (RCLike.ofReal ∘ v)
    with hA₀
  refine ⟨A₀, ?_, ?_, ?_, ?_⟩
  · exact (posSemidef_diagonal_real_iff _).mpr (by
      intro i
      fin_cases i <;> norm_num [hv])
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [hA₀, Matrix.diagonal_apply_eq, hv] at h00
  · have htr : (A₀.trace).re = 1 := by
      rw [hA₀, Matrix.trace_diagonal, Fin.sum_univ_two]
      simp [hv]
    have hnorm : ‖A₀‖ = 1 := by
      rw [hA₀, Matrix.l2_opNorm_diagonal]
      refine le_antisymm ?_ ?_
      · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
        fin_cases i <;> simp [hv]
      · calc (1 : ℝ) = ‖(RCLike.ofReal ∘ v) 0‖ := by
              norm_num [hv, RCLike.norm_ofReal]
          _ ≤ _ := norm_le_pi_norm (RCLike.ofReal ∘ v) (0 : Fin 2)
    have hrank : A₀.rank = 1 := by
      rw [hA₀, Matrix.rank_diagonal, Fintype.card_subtype]
      have hset : Finset.univ.filter
          (fun i => (RCLike.ofReal ∘ v) i ≠ (0 : ℂ)) = {0} := by
        ext j
        fin_cases j <;> simp [Finset.mem_filter, hv]
      rw [hset, Finset.card_singleton]
    rw [intdim, htr, hnorm, hrank]
    norm_num
  · intro c h
    have h00 := congrFun (congrFun h 0) 0
    have h11 := congrFun (congrFun h 1) 1
    simp [hA₀, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Complex.real_smul, hv] at h00 h11
    exact one_ne_zero ((h00.trans h11.symm : (1 : ℂ) = 0))

/-- **Book §7.1** (C7-06): "The intrinsic dimension is *not* monotone with
respect to the semidefinite order.  Indeed, we can drive the intrinsic
dimension to one by increasing one eigenvalue of `A` substantially."
Witness: `1 ≼ diag(3,1)` with `intdim(1) = 2 > 4/3 = intdim(diag(3,1))`.
Implicit source claim. -/
theorem intdim_not_monotone :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A.PosSemidef ∧ B.PosSemidef ∧
      A ≤ B ∧ intdim B < intdim A := by
  set w : Fin 2 → ℝ := ![3, 1] with hw
  set B₀ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (RCLike.ofReal ∘ w)
    with hB₀
  refine ⟨1, B₀, Matrix.PosSemidef.one, ?_, ?_, ?_⟩
  · exact (posSemidef_diagonal_real_iff _).mpr (by
      intro i
      fin_cases i <;> norm_num [hw])
  · rw [Matrix.le_iff]
    have hdiff : B₀ - 1 = Matrix.diagonal (RCLike.ofReal ∘ ![(2 : ℝ), 0]) := by
      rw [hB₀, ← Matrix.diagonal_one, Matrix.diagonal_sub]
      congr 1
      funext i
      fin_cases i <;> norm_num [hw]
    rw [hdiff]
    exact (posSemidef_diagonal_real_iff _).mpr (by
      intro i
      fin_cases i <;> norm_num)
  · have htr : (B₀.trace).re = 4 := by
      rw [hB₀, Matrix.trace_diagonal, Fin.sum_univ_two]
      simp [hw]
      norm_num
    have hnorm : ‖B₀‖ = 3 := by
      rw [hB₀, Matrix.l2_opNorm_diagonal]
      refine le_antisymm ?_ ?_
      · refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
        fin_cases i <;> simp [hw]
      · calc (3 : ℝ) = ‖(RCLike.ofReal ∘ w) 0‖ := by
              norm_num [hw, RCLike.norm_ofReal]
          _ ≤ _ := norm_le_pi_norm (RCLike.ofReal ∘ w) (0 : Fin 2)
    rw [intdim, htr, hnorm, intdim_one]
    norm_num

end Counterexamples

section Blocks

/-- Lean implementation helper: the trace of a block-diagonal matrix is the
sum of the block traces. -/
lemma trace_fromBlocks_diag (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    (Matrix.fromBlocks A 0 0 D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

/-- Lean implementation helper: a block-diagonal matrix with psd blocks is
psd. -/
lemma posSemidef_fromBlocks_diag {A : Matrix m m ℂ} {D : Matrix n n ℂ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  rw [posSemidef_iff_isHermitian_quadratic]
  constructor
  · change (Matrix.fromBlocks A 0 0 D)ᴴ = _
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_zero, hA.1.eq, hD.1.eq]
  · intro u
    have hsplit : star u ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ u) =
        star (u ∘ Sum.inl) ⬝ᵥ (A *ᵥ (u ∘ Sum.inl)) +
          star (u ∘ Sum.inr) ⬝ᵥ (D *ᵥ (u ∘ Sum.inr)) := by
      rw [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.zero_mulVec,
        add_zero, zero_add]
      simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Pi.star_apply, Function.comp_apply]
    rw [hsplit, Complex.add_re]
    have h1 := (posSemidef_iff_isHermitian_quadratic.mp hA).2 (u ∘ Sum.inl)
    have h2 := (posSemidef_iff_isHermitian_quadratic.mp hD).2 (u ∘ Sum.inr)
    exact add_nonneg h1 h2

variable {V₁ : Matrix m m ℂ} {V₂ : Matrix n n ℂ}

/-- **Book §7.3.1 display** (C7-19): the block-diagonal intrinsic dimension in
(7.3.1) is `d = (tr V₁ + tr V₂)/max{‖V₁‖, ‖V₂‖}`.  Explicit (unnumbered)
source display. -/
theorem intdim_fromBlocks_eq (V₁ : Matrix m m ℂ) (V₂ : Matrix n n ℂ) :
    intdim (Matrix.fromBlocks V₁ 0 0 V₂) =
      ((V₁.trace).re + (V₂.trace).re) / max ‖V₁‖ ‖V₂‖ := by
  rw [intdim, trace_fromBlocks_diag, Complex.add_re,
    l2_opNorm_fromBlocks_diagonal]

/-- **Book §7.3.1, intrinsic-dimension bounds**, upper half (C7-18):
`intdim(diag(V₁,V₂)) ≤ intdim(V₁) + intdim(V₂)`.  Explicit source display. -/
theorem intdim_fromBlocks_le_add (hV₁ : V₁.PosSemidef) (hV₂ : V₂.PosSemidef) :
    intdim (Matrix.fromBlocks V₁ 0 0 V₂) ≤ intdim V₁ + intdim V₂ := by
  rw [intdim_fromBlocks_eq, add_div]
  have htr₁ : 0 ≤ (V₁.trace).re := by
    rw [trace_re_eq_sum_eigenvalues hV₁.1]
    exact Finset.sum_nonneg fun i _ => hV₁.eigenvalues_nonneg i
  have htr₂ : 0 ≤ (V₂.trace).re := by
    rw [trace_re_eq_sum_eigenvalues hV₂.1]
    exact Finset.sum_nonneg fun i _ => hV₂.eigenvalues_nonneg i
  refine add_le_add ?_ ?_
  · rcases eq_or_lt_of_le (norm_nonneg V₁) with h0 | hpos
    · have hV₁0 : V₁ = 0 := norm_eq_zero.mp h0.symm
      rw [hV₁0, intdim_zero, Matrix.trace_zero]
      simp
    · rw [intdim]
      exact div_le_div_of_nonneg_left htr₁ hpos (le_max_left _ _)
  · rcases eq_or_lt_of_le (norm_nonneg V₂) with h0 | hpos
    · have hV₂0 : V₂ = 0 := norm_eq_zero.mp h0.symm
      rw [hV₂0, intdim_zero, Matrix.trace_zero]
      simp
    · rw [intdim]
      exact div_le_div_of_nonneg_left htr₂ hpos (le_max_right _ _)

/-- **Book §7.3.1, intrinsic-dimension bounds**, lower half (C7-18):
`min{intdim V₁, intdim V₂} ≤ intdim(diag(V₁,V₂))`.  Explicit source
display. -/
theorem min_intdim_le_intdim_fromBlocks (hV₁ : V₁.PosSemidef)
    (hV₂ : V₂.PosSemidef) :
    min (intdim V₁) (intdim V₂) ≤ intdim (Matrix.fromBlocks V₁ 0 0 V₂) := by
  have htr₁ : 0 ≤ (V₁.trace).re := by
    rw [trace_re_eq_sum_eigenvalues hV₁.1]
    exact Finset.sum_nonneg fun i _ => hV₁.eigenvalues_nonneg i
  have htr₂ : 0 ≤ (V₂.trace).re := by
    rw [trace_re_eq_sum_eigenvalues hV₂.1]
    exact Finset.sum_nonneg fun i _ => hV₂.eigenvalues_nonneg i
  rw [intdim_fromBlocks_eq]
  rcases le_total ‖V₂‖ ‖V₁‖ with hle | hle
  · rw [max_eq_left hle]
    rcases eq_or_lt_of_le (norm_nonneg V₁) with h0 | hpos
    · have hV₁0 : V₁ = 0 := norm_eq_zero.mp h0.symm
      have hV₂0 : V₂ = 0 := norm_eq_zero.mp
        (le_antisymm (hle.trans h0.symm.le) (norm_nonneg _))
      simp [hV₁0, hV₂0, intdim_zero]
    · refine (min_le_left _ _).trans ?_
      rw [intdim]
      gcongr
      linarith
  · rw [max_eq_right hle]
    rcases eq_or_lt_of_le (norm_nonneg V₂) with h0 | hpos
    · have hV₂0 : V₂ = 0 := norm_eq_zero.mp h0.symm
      have hV₁0 : V₁ = 0 := norm_eq_zero.mp
        (le_antisymm (hle.trans h0.symm.le) (norm_nonneg _))
      simp [hV₁0, hV₂0, intdim_zero]
    · refine (min_le_right _ _).trans ?_
      rw [intdim]
      gcongr
      linarith

/-- **Book §7.3.1** (C7-20): "This intrinsic dimension quantity never exceeds
the total of the two side lengths of the random matrix `Z`":
`intdim(diag(V₁,V₂)) ≤ d₁ + d₂`.  Implicit source claim (via
`intdim ≤ rank ≤ dim`). -/
theorem intdim_fromBlocks_le_card [Nonempty m] (hV₁ : V₁.PosSemidef)
    (hV₂ : V₂.PosSemidef) :
    intdim (Matrix.fromBlocks V₁ 0 0 V₂) ≤
      (Fintype.card m : ℝ) + (Fintype.card n : ℝ) := by
  have hpsd := posSemidef_fromBlocks_diag hV₁ hV₂
  calc intdim (Matrix.fromBlocks V₁ 0 0 V₂)
      ≤ ((Matrix.fromBlocks V₁ 0 0 V₂).rank : ℝ) := intdim_le_rank hpsd
    _ ≤ (Fintype.card (m ⊕ n) : ℝ) := by
        exact_mod_cast Nat.cast_le.mpr (Matrix.rank_le_card_width _)
    _ = (Fintype.card m : ℝ) + (Fintype.card n : ℝ) := by
        rw [Fintype.card_sum]
        push_cast
        ring

end Blocks

section StableRank

variable {B : Matrix m n ℂ}

/-- **Book §7.2.2 display** (C7-11): `intdim(BB*) = tr(BB*)/‖BB*‖ =
‖B‖_F²/‖B‖² = srank(B)`.  Explicit source display (the chain identifying the
intrinsic dimension of a Gram matrix with the stable rank). -/
theorem intdim_gram_eq_stableRank (B : Matrix m n ℂ) :
    intdim (B * Bᴴ) = stableRank B := by
  rw [intdim, stableRank, trace_mul_conjTranspose_self, Complex.ofReal_re,
    ← (l2_opNorm_sq_eq B).1]

/-- Lean implementation helper (§7.3.3): the conjugate-transpose Gram variant
`intdim(B*B) = srank(B)`. -/
theorem intdim_gram_conjTranspose_eq_stableRank (B : Matrix m n ℂ) :
    intdim (Bᴴ * B) = stableRank B := by
  have h1 : Bᴴ * B = Bᴴ * (Bᴴ)ᴴ := by rw [Matrix.conjTranspose_conjTranspose]
  rw [h1, intdim_gram_eq_stableRank, stableRank, stableRank,
    frobeniusNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose]

end StableRank

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# Revisiting the matrix Laplace transform bound (Tropp §7.4)

**Book Proposition 7.4.1 (Generalized Matrix Laplace Transform Bound)**: for a
random Hermitian matrix `Y`, a nonnegative
function `ψ : ℝ → ℝ≥0` that is nondecreasing on `[0, ∞)`, and `t ≥ 0`,

`P(λ_max(Y) ≥ t) ≤ (1/ψ(t))·𝔼 tr ψ(Y)`     (`generalized_matrix_laplace_tail`).

`tr ψ(Y)` is rendered as the eigenvalue sum `∑ i, ψ(λ_i(Y))` — the book's
standard matrix function (`trace_cfc_eq_sum` is the bridge to `cfc`).  The
implicit hypotheses `0 < ψ(t)` (the book divides by `ψ(t)`) and integrability
of `tr ψ(Y)` are explicit in Lean.

The adjusted exponentials of §7.4 (C7-29):

* `psiOne θ t = max{0, e^{θt} − 1}` and `psiTwo θ t = e^{θt} − θt − 1`, with
  the prose properties: nonnegative (`psiOne_nonneg`, `psiTwo_nonneg`),
  vanishing at `0` (`psiOne_zero`, `psiTwo_zero`), nondecreasing on the
  positive real line (`psiOne_monotone` — globally, `psiTwo_monotoneOn`),
  and convex (`convexOn_psiOne`, `convexOn_psiTwo`).

Specializations feeding §7.6/§7.7 (C7-35/C7-44), obtained by applying
Proposition 7.4.1 to `θ • Y`:

* `intdim_laplace_psd` — display (7.6-pf-1): for a psd random matrix,
  `P(λ_max(Y) ≥ t) ≤ (e^{θt}−1)⁻¹·𝔼[tr e^{θY} − d]`;
* `intdim_laplace_psiTwo` — display (7.7-pf-1), pointwise form: for a
  Hermitian random matrix,
  `P(λ_max(Y) ≥ t) ≤ (e^{θt}−θt−1)⁻¹·𝔼[tr e^{θY} − θ·tr Y − d]`
  (the caller cancels `𝔼 tr Y = 0` for centered sums).

Scalar toolkit for the §7.6/§7.7 proofs:

* `exp_div_exp_sub_one_le` — `e^a/(e^a−1) ≤ 1 + 1/a` (tangent line at 0);
  the source states it "for a ≥ 0", where `a = 0` is a division by zero;
* `self_le_add_one_mul_log` — `ε ≤ (1+ε)log(1+ε)` (tangent of the convex
  function at 0);
* `exp_taylor_cubic_bound` — `e^a ≥ 1 + a + a²/3 + a³/3` for `a ≥ 0`,
  the content of the book's "numerical fact
  `(e^a−a−1)/a² − (1+a)/3 > 0`"; proved from the degree-4 Taylor partial sum
  (`Real.sum_le_exp_of_nonneg`): the difference is `a²(a−2)²/24 ≥ 0`.
  (The book claims the fact "for all a ∈ ℝ"; under Lean's `0/0`-conventions
  it fails at the removable singularity `a = 0`, and only `a > 0` is used.)
* `exp_div_psiTwo_le` — `e^a/(e^a−a−1) ≤ 1 + 3/a²` for `a > 0`.
-/

namespace MatrixConcentration

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable [IsProbabilityMeasure μ]
variable {Y : Ω → Matrix n n ℂ}

section AdjustedExponentials

/-- **Book §7.4 display** (C7-29): the adjusted exponential
`ψ₁(t) = max{0, e^{θt} − 1}`. -/
noncomputable def psiOne (θ t : ℝ) : ℝ := max 0 (Real.exp (θ * t) - 1)

/-- **Book §7.4 display** (C7-29): the adjusted exponential
`ψ₂(t) = e^{θt} − θt − 1`. -/
noncomputable def psiTwo (θ t : ℝ) : ℝ := Real.exp (θ * t) - θ * t - 1

/-- **Book §7.4** (C7-29): `ψ₁` is nonnegative. -/
lemma psiOne_nonneg (θ t : ℝ) : 0 ≤ psiOne θ t := le_max_left _ _

/-- **Book §7.4** (C7-29): `ψ₂` is nonnegative (from `1 + a ≤ e^a`). -/
lemma psiTwo_nonneg (θ t : ℝ) : 0 ≤ psiTwo θ t := by
  have h := Real.add_one_le_exp (θ * t)
  rw [psiTwo]
  linarith

/-- **Book §7.4** (C7-29): `ψ₁(0) = 0`. -/
lemma psiOne_zero (θ : ℝ) : psiOne θ 0 = 0 := by
  simp [psiOne]

/-- **Book §7.4** (C7-29): `ψ₂(0) = 0`. -/
lemma psiTwo_zero (θ : ℝ) : psiTwo θ 0 = 0 := by
  simp [psiTwo]

/-- **Book §7.4** (C7-29): `ψ₁` is nondecreasing (for `θ ≥ 0`, globally — in
particular on the positive real line, as the book asserts). -/
lemma psiOne_monotone {θ : ℝ} (hθ : 0 ≤ θ) : Monotone (psiOne θ) := by
  intro a b hab
  refine max_le_max le_rfl (sub_le_sub_right ?_ 1)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hθ)

/-- **Book §7.4** (C7-29): `ψ₂` is nondecreasing on the positive real line
(for `θ ≥ 0`). -/
lemma psiTwo_monotoneOn {θ : ℝ} (hθ : 0 ≤ θ) :
    MonotoneOn (psiTwo θ) (Set.Ici 0) := by
  intro a ha b hb hab
  have hθa : 0 ≤ θ * a := mul_nonneg hθ ha
  have hab' : θ * a ≤ θ * b := mul_le_mul_of_nonneg_left hab hθ
  have h1 : Real.exp (θ * a) * ((θ * b - θ * a) + 1) ≤
      Real.exp (θ * a) * Real.exp (θ * b - θ * a) :=
    mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
  rw [← Real.exp_add] at h1
  have h2 : θ * a + (θ * b - θ * a) = θ * b := by ring
  rw [h2] at h1
  have h3 : 1 ≤ Real.exp (θ * a) := Real.one_le_exp hθa
  rw [psiTwo, psiTwo]
  nlinarith [h1, h3, sub_nonneg.mpr hab']

/-- **Book §7.4** (C7-29): `ψ₁` is convex. -/
lemma convexOn_psiOne (θ : ℝ) : ConvexOn ℝ Set.univ (psiOne θ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hexp := convexOn_exp.2 (Set.mem_univ (θ * x)) (Set.mem_univ (θ * y))
    ha hb hab
  have harg : a • (θ * x) + b • (θ * y) = θ * (a • x + b • y) := by
    simp only [smul_eq_mul]
    ring
  rw [harg] at hexp
  simp only [smul_eq_mul] at hexp ⊢
  refine max_le ?_ ?_
  · have h1 : 0 ≤ a * psiOne θ x := mul_nonneg ha (psiOne_nonneg θ x)
    have h2 : 0 ≤ b * psiOne θ y := mul_nonneg hb (psiOne_nonneg θ y)
    linarith
  · have h1 : Real.exp (θ * x) - 1 ≤ psiOne θ x := le_max_right _ _
    have h2 : Real.exp (θ * y) - 1 ≤ psiOne θ y := le_max_right _ _
    have h3 : a * (Real.exp (θ * x) - 1) ≤ a * psiOne θ x :=
      mul_le_mul_of_nonneg_left h1 ha
    have h4 : b * (Real.exp (θ * y) - 1) ≤ b * psiOne θ y :=
      mul_le_mul_of_nonneg_left h2 hb
    nlinarith [hexp]

/-- **Book §7.4** (C7-29): `ψ₂` is convex. -/
lemma convexOn_psiTwo (θ : ℝ) : ConvexOn ℝ Set.univ (psiTwo θ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hexp := convexOn_exp.2 (Set.mem_univ (θ * x)) (Set.mem_univ (θ * y))
    ha hb hab
  have harg : a • (θ * x) + b • (θ * y) = θ * (a • x + b • y) := by
    simp only [smul_eq_mul]
    ring
  rw [harg] at hexp
  simp only [smul_eq_mul] at hexp ⊢
  rw [psiTwo, psiTwo, psiTwo]
  nlinarith [hexp]

end AdjustedExponentials

section ScalarToolkit

/-- **Book §7.6 display** (C7-38): `e^a/(e^a − 1) ≤ 1 + 1/a` — "We obtain the
latter inequality by replacing the convex function `a ↦ e^a − 1` with its
tangent line at `a = 0`."  Stated in the source "for `a ≥ 0`"; at `a = 0`
both sides involve division by zero, so the Lean statement carries `0 < a`.

**Author note.** This positivity hypothesis is the well-defined Lean form of the
source inequality. -/
lemma exp_div_exp_sub_one_le {a : ℝ} (ha : 0 < a) :
    Real.exp a / (Real.exp a - 1) ≤ 1 + 1 / a := by
  have h1 : a + 1 ≤ Real.exp a := Real.add_one_le_exp a
  have hE : 0 < Real.exp a - 1 := by linarith
  have key : Real.exp a * a ≤ (a + 1) * (Real.exp a - 1) := by nlinarith
  calc Real.exp a / (Real.exp a - 1)
      = Real.exp a * a / ((Real.exp a - 1) * a) := by
        rw [mul_div_mul_right _ _ ha.ne']
    _ ≤ (a + 1) * (Real.exp a - 1) / ((Real.exp a - 1) * a) := by gcongr
    _ = (a + 1) / a := by
        rw [mul_comm (a + 1) (Real.exp a - 1), mul_div_mul_left _ _ hE.ne']
    _ = 1 + 1 / a := by
        rw [add_div, div_self ha.ne']

/-- **Book §7.6** (C7-40): `(1+ε)log(1+ε) ≥ ε` — "The function
`a ↦ (1+a)log(1+a)` is convex … we can bound it below using its tangent at
`ε = 0`."  Explicit source display (proved via `log x ≤ x − 1` at
`x = 1/(1+ε)`). -/
lemma self_le_add_one_mul_log {ε : ℝ} (hε : 0 ≤ ε) :
    ε ≤ (1 + ε) * Real.log (1 + ε) := by
  have h1 : 0 < 1 + ε := by linarith
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  rw [Real.log_inv] at h2
  have h3 : ε / (1 + ε) ≤ Real.log (1 + ε) := by
    have h4 : (1 + ε)⁻¹ - 1 = -(ε / (1 + ε)) := by
      field_simp
      ring
    rw [h4] at h2
    linarith
  calc ε = (1 + ε) * (ε / (1 + ε)) := by
        field_simp
    _ ≤ (1 + ε) * Real.log (1 + ε) := by
        exact mul_le_mul_of_nonneg_left h3 h1.le

/-- **Book §7.7 "numerical fact"** (C7-47): the content of the display
`(e^a − a − 1)/a² − (1+a)/3 > 0`, in the division-free form
`e^a ≥ 1 + a + a²/3 + a³/3` for `a ≥ 0`.  The source justifies it by
convexity and a numerical minimum "attained near `a ≈ 1.30`"; the Lean proof
uses the degree-4 Taylor partial sum (`Real.sum_le_exp_of_nonneg`), whose
excess over the cubic is exactly `a²(a−2)²/24 ≥ 0`.  (The book claims the
fact "for all `a ∈ ℝ`"; at `a = 0` the divided form is a removable
singularity that fails under Lean's `0/0 = 0`, and only `a ≥ 0` is used.)

**Author note.** The division-free statement records the removable singularity
without changing the inequality used in the proof. -/
lemma exp_taylor_cubic_bound {a : ℝ} (ha : 0 ≤ a) :
    1 + a + a ^ 2 / 3 + a ^ 3 / 3 ≤ Real.exp a := by
  have h := Real.sum_le_exp_of_nonneg ha 5
  have hsum : ∑ i ∈ Finset.range 5, a ^ i / (Nat.factorial i : ℝ) =
      1 + a + a ^ 2 / 2 + a ^ 3 / 6 + a ^ 4 / 24 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
  rw [hsum] at h
  nlinarith [sq_nonneg (a * (a - 2)), h]

/-- **Book §7.7 display** (C7-47): `e^a/(e^a − a − 1) ≤ 1 + 3/a²` for
`a > 0` (the source's "for all `a ≥ 0`" involves division by zero at `a = 0`).

**Author note.** The strict hypothesis is the well-defined form needed by the
source argument. -/
lemma exp_div_psiTwo_le {a : ℝ} (ha : 0 < a) :
    Real.exp a / (Real.exp a - a - 1) ≤ 1 + 3 / a ^ 2 := by
  have hD : 0 < Real.exp a - a - 1 := by
    have := Real.add_one_lt_exp (ne_of_gt ha)
    linarith
  have hsq : 0 < a ^ 2 := by positivity
  have htaylor := exp_taylor_cubic_bound ha.le
  -- `a²·e^a ≤ (a² + 3)·(e^a − a − 1)` ⟺ `a³ + a² ≤ 3(e^a − a − 1)`
  have key : a ^ 2 * Real.exp a ≤ (a ^ 2 + 3) * (Real.exp a - a - 1) := by
    nlinarith [htaylor]
  calc Real.exp a / (Real.exp a - a - 1)
      = a ^ 2 * Real.exp a / (a ^ 2 * (Real.exp a - a - 1)) := by
        rw [mul_div_mul_left _ _ hsq.ne']
    _ ≤ (a ^ 2 + 3) * (Real.exp a - a - 1) /
          (a ^ 2 * (Real.exp a - a - 1)) := by gcongr
    _ = (a ^ 2 + 3) / a ^ 2 := by
        rw [mul_comm (a ^ 2) (Real.exp a - a - 1),
          mul_comm (a ^ 2 + 3) (Real.exp a - a - 1),
          mul_div_mul_left _ _ hD.ne']
    _ = 1 + 3 / a ^ 2 := by
        rw [add_div, div_self hsq.ne']

end ScalarToolkit

section GeneralizedLaplace

variable [Nonempty n]

/-- **Book §7.4, proof of Proposition 7.4.1** (C7-31): the trace of `ψ(Y)`
dominates `ψ(λ_max(Y))` — the source's chain "`λ_max(ψ(Y)) ≥ ψ(λ_max(Y))`
by the Spectral Mapping Theorem, and the trace dominates the maximum
eigenvalue of the psd matrix `ψ(Y)`", at the eigenvalue-sum level.  Implicit
source claim. -/
lemma psi_lambdaMax_le_sum {ψ : ℝ → ℝ} (hψ0 : ∀ s, 0 ≤ ψ s)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ψ (lambdaMax hA) ≤ ∑ i, ψ (hA.eigenvalues i) := by
  obtain ⟨i₀, hi₀⟩ := exists_eigenvalues_eq_lambdaMax hA
  calc ψ (lambdaMax hA) = ψ (hA.eigenvalues i₀) := by rw [hi₀]
    _ ≤ ∑ i, ψ (hA.eigenvalues i) :=
        Finset.single_le_sum (fun i _ => hψ0 _) (Finset.mem_univ i₀)

/-- **Book Proposition 7.4.1 (Generalized Matrix Laplace Transform Bound)**:
for a random Hermitian matrix `Y`, a nonnegative
function `ψ` nondecreasing on `[0, ∞)`, and `t ≥ 0`,

`P(λ_max(Y) ≥ t) ≤ (1/ψ(t))·𝔼 tr ψ(Y)`,

where `tr ψ(Y) = ∑ i, ψ(λ_i(Y))` (the standard matrix function;
`trace_cfc_eq_sum`).  The book's `1/ψ(t)` presumes `0 < ψ(t)` and the
expectation presumes integrability; both are explicit hypotheses in Lean.
Explicit source declaration with proof (Markov's inequality
after the spectral-mapping comparison `psi_lambdaMax_le_sum`). -/
theorem generalized_matrix_laplace_tail
    {ψ : ℝ → ℝ} (hψ0 : ∀ s, 0 ≤ ψ s) (hmono : MonotoneOn ψ (Set.Ici 0))
    (hY : ∀ ω, (Y ω).IsHermitian) {t : ℝ} (ht : 0 ≤ t) (hψt : 0 < ψ t)
    (hint : Integrable (fun ω => ∑ i, ψ ((hY ω).eigenvalues i)) μ) :
    μ.real {ω | t ≤ lambdaMax (hY ω)} ≤
      (ψ t)⁻¹ * ∫ ω, ∑ i, ψ ((hY ω).eigenvalues i) ∂μ := by
  have hsub : {ω | t ≤ lambdaMax (hY ω)} ⊆
      {ω | ψ t ≤ ∑ i, ψ ((hY ω).eigenvalues i)} := by
    intro ω hω
    have h1 : ψ t ≤ ψ (lambdaMax (hY ω)) :=
      hmono ht (Set.mem_Ici.mpr (ht.trans hω)) hω
    exact h1.trans (psi_lambdaMax_le_sum hψ0 (hY ω))
  have hmarkov := markov_inequality (μ := μ)
    (Filter.Eventually.of_forall fun ω =>
      Finset.sum_nonneg fun i _ => hψ0 _) hint hψt
  calc μ.real {ω | t ≤ lambdaMax (hY ω)}
      ≤ μ.real {ω | ψ t ≤ ∑ i, ψ ((hY ω).eigenvalues i)} :=
        measureReal_mono hsub
    _ ≤ (∫ ω, ∑ i, ψ ((hY ω).eigenvalues i) ∂μ) / ψ t := hmarkov
    _ = (ψ t)⁻¹ * ∫ ω, ∑ i, ψ ((hY ω).eigenvalues i) ∂μ := by
        rw [div_eq_inv_mul]

end GeneralizedLaplace

section Specializations

variable [Nonempty n]

/-- Lean implementation helper: measurability of `ω ↦ (tr Y(ω)).re`. -/
lemma measurable_trace_re (hYm : Measurable Y) :
    Measurable fun ω => ((Y ω).trace).re := by
  have h1 : (fun ω => ((Y ω).trace).re) =
      fun ω => ∑ i, ((Y ω) i i).re := by
    funext ω
    rw [Matrix.trace, Complex.re_sum]
    rfl
  rw [h1]
  exact Finset.measurable_sum _ fun i _ =>
    Complex.measurable_re.comp ((measurable_entry i i).comp hYm)

/-- Lean implementation helper: integrability of `ω ↦ (tr Y(ω)).re` under a
uniform norm bound. -/
lemma integrable_trace_re (hYm : Measurable Y) {R : ℝ}
    (hR : ∀ ω, ‖Y ω‖ ≤ R) :
    Integrable (fun ω => ((Y ω).trace).re) μ := by
  refine Integrable.of_bound (measurable_trace_re hYm).aestronglyMeasurable
    ((Fintype.card n : ℝ) * R) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have h1 : |((Y ω).trace).re| ≤ ∑ i : n, ‖(Y ω) i i‖ := by
    rw [Matrix.trace, Complex.re_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun i _ => Complex.abs_re_le_norm _
  refine h1.trans ?_
  calc (∑ i : n, ‖(Y ω) i i‖) ≤ ∑ _i : n, R :=
        Finset.sum_le_sum fun i _ =>
          (norm_entry_le_l2_opNorm _ i i).trans (hR ω)
    _ = (Fintype.card n : ℝ) * R := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Book §7.6, display (7.6.1)** (C7-35): the `ψ₁`-specialization of
Proposition 7.4.1 for a psd random matrix — "We have exploited the fact that
`Y` is positive semidefinite and the assumption that `t ≥ 0`":

`P(λ_max(Y) ≥ t) ≤ (e^{θt} − 1)⁻¹ · 𝔼 tr(e^{θY} − I)`.

Implicit source display.

**Author note.** Lean states `t > 0` explicitly because the displayed denominator
requires `ψ₁(t) > 0`. -/
theorem intdim_laplace_psd (hYm : Measurable Y)
    (hpsd : ∀ ω, (Y ω).PosSemidef) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R)
    {t θ : ℝ} (ht : 0 < t) (hθ : 0 < θ) :
    μ.real {ω | t ≤ lambdaMax (hpsd ω).1} ≤
      (Real.exp (θ * t) - 1)⁻¹ *
        ∫ ω, (((NormedSpace.exp (θ • Y ω)).trace).re - (Fintype.card n : ℝ))
          ∂μ := by
  have hWherm : ∀ ω, (θ • Y ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hpsd ω).1 θ
  have hWpsd : ∀ ω, (θ • Y ω).PosSemidef := fun ω =>
    posSemidef_smul_nonneg (hpsd ω) hθ.le
  -- the integrand identity: `Σ ψ₁(λ_i(θY)) = tr e^{θY} − d`
  have hpoint : ∀ ω, ∑ i, psiOne 1 ((hWherm ω).eigenvalues i) =
      ((NormedSpace.exp (θ • Y ω)).trace).re - (Fintype.card n : ℝ) := by
    intro ω
    have h1 : ∀ i, psiOne 1 ((hWherm ω).eigenvalues i) =
        Real.exp ((hWherm ω).eigenvalues i) - 1 := by
      intro i
      rw [psiOne, one_mul, max_eq_right]
      have h2 : 0 ≤ (hWherm ω).eigenvalues i := (hWpsd ω).eigenvalues_nonneg i
      have h3 : (1 : ℝ) ≤ Real.exp ((hWherm ω).eigenvalues i) :=
        Real.one_le_exp h2
      linarith
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      trace_exp_re_eq_sum (hWherm ω)]
  -- event conversion `{t ≤ λ_max(Y)} = {θt ≤ λ_max(θY)}`
  have hevent : {ω | t ≤ lambdaMax (hpsd ω).1} =
      {ω | θ * t ≤ lambdaMax (hWherm ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [lambdaMax_smul_nonneg (hpsd ω).1 hθ.le (hWherm ω)]
    exact ⟨fun h => mul_le_mul_of_nonneg_left h hθ.le,
      fun h => le_of_mul_le_mul_left h hθ⟩
  have hψt : 0 < psiOne 1 (θ * t) := by
    rw [psiOne, one_mul]
    have h1 : 1 < Real.exp (θ * t) := by
      nlinarith [Real.add_one_lt_exp (ne_of_gt (mul_pos hθ ht))]
    exact lt_max_of_lt_right (by linarith)
  have hint : Integrable
      (fun ω => ∑ i, psiOne 1 ((hWherm ω).eigenvalues i)) μ := by
    rw [show (fun ω => ∑ i, psiOne 1 ((hWherm ω).eigenvalues i)) =
        fun ω => ((NormedSpace.exp (θ • Y ω)).trace).re - (Fintype.card n : ℝ)
      from funext hpoint]
    exact (integrable_trace_exp_re (μ := μ) (hYm.const_smul θ) hWherm
      (norm_smul_le_of_bound hR)).sub (integrable_const _)
  have h := generalized_matrix_laplace_tail (μ := μ)
    (fun s => psiOne_nonneg 1 s) ((psiOne_monotone zero_le_one).monotoneOn _)
    hWherm (mul_nonneg hθ.le ht.le) hψt hint
  rw [hevent]
  refine h.trans ?_
  rw [psiOne, one_mul, max_eq_right (by
    have h1 : 1 ≤ Real.exp (θ * t) := Real.one_le_exp (mul_nonneg hθ.le ht.le)
    linarith)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by
    have h1 : 1 ≤ Real.exp (θ * t) := Real.one_le_exp (mul_nonneg hθ.le ht.le)
    linarith))
  refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall ?_))
  exact hpoint

/-- **Book §7.7, display (7.7-pf-1)** (C7-44): the `ψ₂`-specialization of
Proposition 7.4.1 for a Hermitian random matrix, in pointwise form:

`P(λ_max(Y) ≥ t) ≤ (e^{θt} − θt − 1)⁻¹ · 𝔼[tr e^{θY} − θ·tr Y − I]`.

The book's display continues `= (…)⁻¹·𝔼 tr(e^{θY} − I)` "because the random
matrix `Y` has zero mean"; the cancellation `𝔼 tr Y = 0` happens at the call
site (file 06).  Implicit source display.

**Author note.** This pointwise-support form is retained for compatibility;
see `intdim_laplace_psiTwo_one_sided` for the one-sided/a.e. counterpart. -/
theorem intdim_laplace_psiTwo (hYm : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R)
    {t θ : ℝ} (ht : 0 < t) (hθ : 0 < θ) :
    μ.real {ω | t ≤ lambdaMax (hHerm ω)} ≤
      (Real.exp (θ * t) - θ * t - 1)⁻¹ *
        ∫ ω, (((NormedSpace.exp (θ • Y ω)).trace).re -
          θ * ((Y ω).trace).re - (Fintype.card n : ℝ)) ∂μ := by
  have hWherm : ∀ ω, (θ • Y ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hHerm ω) θ
  -- the integrand identity: `Σ ψ₂(λ_i(θY)) = tr e^{θY} − θ·tr Y − d`
  have hpoint : ∀ ω, ∑ i, psiTwo 1 ((hWherm ω).eigenvalues i) =
      ((NormedSpace.exp (θ • Y ω)).trace).re - θ * ((Y ω).trace).re -
        (Fintype.card n : ℝ) := by
    intro ω
    have h1 : ∀ i, psiTwo 1 ((hWherm ω).eigenvalues i) =
        Real.exp ((hWherm ω).eigenvalues i) - (hWherm ω).eigenvalues i - 1 :=
      fun i => by rw [psiTwo, one_mul]
    have htrW : ∑ i, (hWherm ω).eigenvalues i = θ * ((Y ω).trace).re := by
      rw [← trace_re_eq_sum_eigenvalues (hWherm ω), Matrix.trace_smul,
        Complex.smul_re, smul_eq_mul]
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    rw [show (fun i => Real.exp ((hWherm ω).eigenvalues i) -
        (hWherm ω).eigenvalues i - 1) = fun i =>
        (Real.exp ((hWherm ω).eigenvalues i) - (hWherm ω).eigenvalues i) - 1
      from rfl, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, htrW,
      trace_exp_re_eq_sum (hWherm ω)]
  have hevent : {ω | t ≤ lambdaMax (hHerm ω)} =
      {ω | θ * t ≤ lambdaMax (hWherm ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [lambdaMax_smul_nonneg (hHerm ω) hθ.le (hWherm ω)]
    exact ⟨fun h => mul_le_mul_of_nonneg_left h hθ.le,
      fun h => le_of_mul_le_mul_left h hθ⟩
  have hψt : 0 < psiTwo 1 (θ * t) := by
    rw [psiTwo, one_mul]
    have h1 := Real.add_one_lt_exp (ne_of_gt (mul_pos hθ ht))
    linarith
  have hint : Integrable
      (fun ω => ∑ i, psiTwo 1 ((hWherm ω).eigenvalues i)) μ := by
    rw [show (fun ω => ∑ i, psiTwo 1 ((hWherm ω).eigenvalues i)) =
        fun ω => ((NormedSpace.exp (θ • Y ω)).trace).re -
          θ * ((Y ω).trace).re - (Fintype.card n : ℝ)
      from funext hpoint]
    exact (((integrable_trace_exp_re (μ := μ) (hYm.const_smul θ) hWherm
      (norm_smul_le_of_bound hR)).sub
        ((integrable_trace_re hYm hR).const_mul θ)).sub (integrable_const _))
  have h := generalized_matrix_laplace_tail (μ := μ)
    (fun s => psiTwo_nonneg 1 s) (by
      have := psiTwo_monotoneOn (θ := 1) zero_le_one
      exact this)
    hWherm (mul_nonneg hθ.le ht.le) hψt hint
  rw [hevent]
  refine h.trans ?_
  rw [psiTwo, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by
    have h1 := Real.add_one_le_exp (θ * t)
    linarith))
  refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall ?_))
  exact hpoint

end Specializations

end MatrixConcentration

set_option linter.unusedSectionVars false

/-!
# The intrinsic dimension lemma (Tropp §7.5)

**Book Lemma 7.5.1 (Intrinsic Dimension)**: for a convex
function `φ` on `[0, ∞)` with `φ(0) = 0` and a psd matrix `A`,

`tr φ(A) ≤ intdim(A) · φ(‖A‖)`     (`intdim_trace_bound`),

with `tr φ(A) = ∑ i, φ(λ_i(A))` (the standard matrix function;
`trace_cfc_eq_sum` is the bridge to `cfc`).  The proof follows the book: the
chord bound `φ(a) ≤ (a/L)·φ(L)` on `[0, L]` (`convexOn_le_chord`, the
book's "bounded above by the chord connecting the graph at the endpoints"),
applied across the spectrum (the book's Transfer-Rule step), then the
identification `tr A/‖A‖ = intdim(A)`.  The degenerate case `A = 0`
(excluded implicitly by the book) holds under Lean's conventions
because `φ(0) = 0`.

Specialization feeding §7.6–§7.7 (C7-34): `φ(a) = e^a − 1` gives

`tr(e^A − I) ≤ intdim(A)·(e^{‖A‖} − 1)`   (`trace_exp_sub_card_le_intdim`)

and, with the book's "trivial inequality `φ(a) ≤ e^a`",

`tr(e^A − I) ≤ intdim(A)·e^{‖A‖}`   (`trace_exp_sub_card_le_intdim_exp`).
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Book §7.5, proof of Lemma 7.5.1** (C7-33): the chord bound — "Since the
function `a ↦ φ(a)` is convex on the interval `[0, L]`, it is bounded above
by the chord connecting the graph at the endpoints:
`φ(a) ≤ (1 − a/L)·φ(0) + (a/L)·φ(L) = (a/L)·φ(L)`."  Implicit source
display. -/
lemma convexOn_le_chord {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Set.Ici 0) φ)
    (hφ0 : φ 0 = 0) {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (haL : a ≤ L) :
    φ a ≤ a / L * φ L := by
  have hcoeff : 0 ≤ 1 - a / L := by
    rw [sub_nonneg]
    exact (div_le_one hL).mpr haL
  have hcomb := hφ.2 (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
    (Set.mem_Ici.mpr hL.le) hcoeff (by positivity : (0 : ℝ) ≤ a / L)
    (by ring)
  have harg : (1 - a / L) • (0 : ℝ) + (a / L) • L = a := by
    rw [smul_zero, zero_add, smul_eq_mul, div_mul_cancel₀ _ hL.ne']
  rw [harg, hφ0] at hcomb
  simpa using hcomb

/-- **Book Lemma 7.5.1 (Intrinsic Dimension)**: for a
convex function `φ` on `[0, ∞)` with `φ(0) = 0` and a psd matrix `A`,
`tr φ(A) ≤ intdim(A)·φ(‖A‖)`, with `tr φ(A) = ∑ i, φ(λ_i(A))` (the standard
matrix function).  Explicit source declaration with proof (chord bound +
Transfer Rule + identification of the intrinsic dimension). -/
theorem intdim_trace_bound {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Set.Ici 0) φ)
    (hφ0 : φ 0 = 0) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    ∑ i, φ (hA.1.eigenvalues i) ≤ intdim A * φ ‖A‖ := by
  rcases eq_or_lt_of_le (norm_nonneg A) with h0 | hpos
  · -- degenerate case `‖A‖ = 0`: the spectrum vanishes and `φ(0) = 0`
    have hzero : ∀ i, hA.1.eigenvalues i = 0 := by
      intro i
      haveI : Nonempty n := ⟨i⟩
      have h1 := hA.eigenvalues_nonneg i
      have h2 := eigenvalues_le_lambdaMax hA.1 i
      have h3 : lambdaMax hA.1 ≤ ‖A‖ :=
        le_of_eq (posSemidef_l2_opNorm_eq_lambdaMax hA).symm
      rw [← h0] at h3
      linarith
    calc ∑ i, φ (hA.1.eigenvalues i) = ∑ _i : n, (0 : ℝ) :=
          Finset.sum_congr rfl fun i _ => by rw [hzero i, hφ0]
      _ = 0 := Finset.sum_const_zero
      _ ≤ intdim A * φ ‖A‖ := by
          rw [show ‖A‖ = 0 from h0.symm, hφ0, mul_zero]
  · -- chord bound across the spectrum, then identify `intdim`
    have hbound : ∀ i, φ (hA.1.eigenvalues i) ≤
        hA.1.eigenvalues i * (φ ‖A‖ / ‖A‖) := by
      intro i
      haveI : Nonempty n := ⟨i⟩
      have h1 := hA.eigenvalues_nonneg i
      have h2 : hA.1.eigenvalues i ≤ ‖A‖ :=
        (eigenvalues_le_lambdaMax hA.1 i).trans
          (le_of_eq (posSemidef_l2_opNorm_eq_lambdaMax hA).symm)
      calc φ (hA.1.eigenvalues i) ≤ hA.1.eigenvalues i / ‖A‖ * φ ‖A‖ :=
            convexOn_le_chord hφ hφ0 hpos h1 h2
        _ = hA.1.eigenvalues i * (φ ‖A‖ / ‖A‖) := by ring
    calc ∑ i, φ (hA.1.eigenvalues i)
        ≤ ∑ i, hA.1.eigenvalues i * (φ ‖A‖ / ‖A‖) :=
          Finset.sum_le_sum fun i _ => hbound i
      _ = (∑ i, hA.1.eigenvalues i) * (φ ‖A‖ / ‖A‖) :=
          (Finset.sum_mul _ _ _).symm
      _ = intdim A * φ ‖A‖ := by
          rw [intdim, ← trace_re_eq_sum_eigenvalues hA.1]
          ring

/-- **Book Lemma 7.5.1 (Intrinsic Dimension), relaxed hypothesis `φ(0) ≤ 0`.**
For a convex function `φ` on `[0, ∞)` with `φ(0) ≤ 0` and a psd matrix `A`,
`tr φ(A) ≤ intdim(A)·φ(‖A‖)`.  This generalizes `intdim_trace_bound` (the
book's `φ(0) = 0` form): the chord bound
`φ(a) ≤ (1 − a/L)·φ(0) + (a/L)·φ(L)` still yields `φ(a) ≤ (a/L)·φ(L)` because
the dropped term `(1 − a/L)·φ(0)` is nonpositive.  The proof mirrors
`intdim_trace_bound`, applying this relaxed chord bound across the spectrum;
the degenerate case `‖A‖ = 0` uses `φ(0) ≤ 0` together with `card ≥ 0`. -/
theorem intdim_trace_bound_of_nonpos {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ (Set.Ici 0) φ) (hφ0 : φ 0 ≤ 0)
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    ∑ i, φ (hA.1.eigenvalues i) ≤ intdim A * φ ‖A‖ := by
  rcases eq_or_lt_of_le (norm_nonneg A) with h0 | hpos
  · -- degenerate case `‖A‖ = 0`: the spectrum vanishes; use `φ(0) ≤ 0`, `card ≥ 0`
    have hzero : ∀ i, hA.1.eigenvalues i = 0 := by
      intro i
      haveI : Nonempty n := ⟨i⟩
      have h1 := hA.eigenvalues_nonneg i
      have h2 := eigenvalues_le_lambdaMax hA.1 i
      have h3 : lambdaMax hA.1 ≤ ‖A‖ :=
        le_of_eq (posSemidef_l2_opNorm_eq_lambdaMax hA).symm
      rw [← h0] at h3
      linarith
    have hrhs : intdim A * φ ‖A‖ = 0 := by
      rw [intdim, ← h0]; simp
    rw [hrhs]
    calc ∑ i, φ (hA.1.eigenvalues i) = ∑ _i : n, φ 0 :=
          Finset.sum_congr rfl fun i _ => by rw [hzero i]
      _ = (Fintype.card n : ℝ) * φ 0 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 0 := mul_nonpos_iff.mpr (Or.inl ⟨Nat.cast_nonneg _, hφ0⟩)
  · -- relaxed chord bound across the spectrum, then identify `intdim`
    have hbound : ∀ i, φ (hA.1.eigenvalues i) ≤
        hA.1.eigenvalues i * (φ ‖A‖ / ‖A‖) := by
      intro i
      haveI : Nonempty n := ⟨i⟩
      have h1 := hA.eigenvalues_nonneg i
      have h2 : hA.1.eigenvalues i ≤ ‖A‖ :=
        (eigenvalues_le_lambdaMax hA.1 i).trans
          (le_of_eq (posSemidef_l2_opNorm_eq_lambdaMax hA).symm)
      have hcoeff : 0 ≤ 1 - hA.1.eigenvalues i / ‖A‖ := by
        rw [sub_nonneg]; exact (div_le_one hpos).mpr h2
      have hcomb := hφ.2 (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
        (Set.mem_Ici.mpr hpos.le) hcoeff
        (by positivity : (0 : ℝ) ≤ hA.1.eigenvalues i / ‖A‖) (by ring)
      have harg : (1 - hA.1.eigenvalues i / ‖A‖) • (0 : ℝ) +
          (hA.1.eigenvalues i / ‖A‖) • ‖A‖ = hA.1.eigenvalues i := by
        rw [smul_zero, zero_add, smul_eq_mul, div_mul_cancel₀ _ hpos.ne']
      rw [harg] at hcomb
      simp only [smul_eq_mul] at hcomb
      have hnonpos : (1 - hA.1.eigenvalues i / ‖A‖) * φ 0 ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inl ⟨hcoeff, hφ0⟩)
      have hchord : φ (hA.1.eigenvalues i) ≤
          hA.1.eigenvalues i / ‖A‖ * φ ‖A‖ := by linarith [hcomb, hnonpos]
      calc φ (hA.1.eigenvalues i) ≤ hA.1.eigenvalues i / ‖A‖ * φ ‖A‖ := hchord
        _ = hA.1.eigenvalues i * (φ ‖A‖ / ‖A‖) := by ring
    calc ∑ i, φ (hA.1.eigenvalues i)
        ≤ ∑ i, hA.1.eigenvalues i * (φ ‖A‖ / ‖A‖) :=
          Finset.sum_le_sum fun i _ => hbound i
      _ = (∑ i, hA.1.eigenvalues i) * (φ ‖A‖ / ‖A‖) :=
          (Finset.sum_mul _ _ _).symm
      _ = intdim A * φ ‖A‖ := by
          rw [intdim, ← trace_re_eq_sum_eigenvalues hA.1]
          ring

section ExpSpecialization

/-- Lean implementation helper: `a ↦ e^a − 1` is convex on `[0, ∞)`. -/
lemma convexOn_exp_sub_one : ConvexOn ℝ (Set.Ici 0) fun a : ℝ =>
    Real.exp a - 1 := by
  refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
  have hexp := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hexp ⊢
  nlinarith [hexp]

/-- **Book §7.6/§7.7 specialization of Lemma 7.5.1** (C7-34): with
`φ(a) = e^a − 1`, `tr(e^A − I) ≤ intdim(A)·(e^{‖A‖} − 1)` for psd `A`
(the displays "`tr(e^{g(θ)·M} − I) = tr φ(g(θ)·M) ≤ intdim(M)·φ(g(θ)‖M‖)`").
Implicit source display. -/
theorem trace_exp_sub_card_le_intdim {B : Matrix n n ℂ} (hB : B.PosSemidef) :
    ((NormedSpace.exp B).trace).re - (Fintype.card n : ℝ) ≤
      intdim B * (Real.exp ‖B‖ - 1) := by
  have h := intdim_trace_bound convexOn_exp_sub_one (by simp) hB
  have hsplit : ∑ i, (Real.exp (hB.1.eigenvalues i) - 1) =
      (∑ i, Real.exp (hB.1.eigenvalues i)) - (Fintype.card n : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  rw [trace_exp_re_eq_sum hB.1]
  linarith [h, hsplit.symm.le, hsplit.le]

/-- **Book §7.6/§7.7** (C7-37/C7-46): combining C7-34 with "the trivial
inequality `φ(a) ≤ e^a`, which holds for `a ∈ ℝ`":
`tr(e^A − I) ≤ intdim(A)·e^{‖A‖}` for psd `A`.  Implicit source display. -/
theorem trace_exp_sub_card_le_intdim_exp {B : Matrix n n ℂ}
    (hB : B.PosSemidef) :
    ((NormedSpace.exp B).trace).re - (Fintype.card n : ℝ) ≤
      intdim B * Real.exp ‖B‖ := by
  refine (trace_exp_sub_card_le_intdim hB).trans ?_
  have h1 : Real.exp ‖B‖ - 1 ≤ Real.exp ‖B‖ := by linarith
  exact mul_le_mul_of_nonneg_left h1 (intdim_nonneg hB)

end ExpSpecialization

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Matrix Chernoff with intrinsic dimension: Theorem 7.2.1 (Tropp §7.2, §7.6)

**Book Theorem 7.2.1 (Matrix Chernoff: Intrinsic Dimension)**: for independent
random Hermitian matrices with
`0 ≤ λ_min(X_k)` and `λ_max(X_k) ≤ L`, `Y = Σ X_k`, and a semidefinite upper
bound `M ≽ 𝔼Y`, with `d = intdim(M)` and `μ_max = λ_max(M)`:

* **Book equation (7.2.1)**: for `θ > 0`,
  `𝔼 λ_max(Y) ≤ ((e^θ − 1)/θ)·μ_max + (1/θ)·L·log(2d)`
  (`intdim_chernoff_expectation`);
* **Book equation (7.2.2)**: for `ε ≥ L/μ_max`,
  `P(λ_max(Y) ≥ (1+ε)μ_max) ≤ 2d·[e^ε/(1+ε)^{1+ε}]^{μ_max/L}`
  (`intdim_chernoff_tail`).

Proof per §7.6: the `ψ₁`-specialization of the generalized Laplace transform
bound (`intdim_laplace_psd`, file 02), the Chernoff trace-mgf bound
`𝔼 tr e^{θY} ≤ tr exp(g(θ)·𝔼Y)` with `g(θ) = (e^{θL} − 1)/L`
(`chernoff_trace_mgf_bound`, C7-36 — "As in the proof of the original matrix
Chernoff bound"), the intrinsic dimension lemma (file 03), and the scalar
estimates `e^a/(e^a−1) ≤ 1 + 1/a` and `(1+ε)log(1+ε) ≥ ε` (file 02).  The
expectation bound integrates the pointwise identity
`λ_max(Y) = ψ⁻¹(ψ(λ_max(Y)))` with `ψ⁻¹(u) = θ⁻¹ log(1+u)` and Jensen's
inequality for the logarithm (`integral_log_le_log_integral`, Chapter 3).

The implicit nondegeneracy hypotheses are
explicit — `M ≠ 0` (`intdim M` is a `0/0` otherwise, and the proof uses
`d ≥ 1`) and `0 < L` (the book's `μ_max/L` exponent and `ε ≥ L/μ_max`
presume it).  `M.PosSemidef` is the book's own "semidefinite upper bound".

-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {X : ι → Ω → Matrix n n ℂ} {L : ℝ} {M : Matrix n n ℂ}

section TraceMgf

/-- **Book §7.6, first display of the proof** (C7-36): "As in the proof of
the original matrix Chernoff bound, Theorem 5.1.1, we have the estimate
`𝔼 tr e^{θY} ≤ tr exp(g(θ)·𝔼Y)` where `g(θ) = (e^{θL} − 1)/L`."  Implicit
source display (the Chapter-5 chain, stopped before the `tr ≤ d·λ_max`
step).

**Author note.** This pointwise-support form is retained for compatibility;
see `chernoff_trace_mgf_bound_ae` for the source-faithful almost-sure
counterpart. -/
lemma chernoff_trace_mgf_bound
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L)
    (hindep : ProbabilityTheory.iIndepFun X μ) (hL : 0 < L) (θ : ℝ) :
    ∫ ω, ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re ∂μ ≤
      ((NormedSpace.exp (gChernoff θ L • ∑ k, expectation μ (X k))).trace).re
      := by
  have hR : ∀ k ω, ‖X k ω‖ ≤ (fun _ : ι => L) k := fun k ω =>
    l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
  have h1 := trace_exp_sum_le_trace_exp_sum_cgf (μ := μ) hmeas hherm hR
    hindep θ
  have hrw : (fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re) =
      fun ω => ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re := by
    funext ω
    rw [Finset.smul_sum]
  rw [hrw]
  refine h1.trans ?_
  have hcgf_le : ∀ k, matrixCgf μ (X k) θ ≤
      gChernoff θ L • expectation μ (X k) := fun k =>
    chernoff_matrix_cgf_le (μ := μ) (hmeas k) (hherm k) (hmin k) (hmax k)
      hL.le θ
  have hsum_le : (∑ k, matrixCgf μ (X k) θ) ≤
      gChernoff θ L • ∑ k, expectation μ (X k) := by
    rw [Finset.smul_sum]
    exact sum_loewner_mono Finset.univ fun k _ => hcgf_le k
  have hcgfHerm : (∑ k, matrixCgf μ (X k) θ).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => isHermitian_cfc_log _
  have hEsumHerm : (∑ k, expectation μ (X k)).IsHermitian :=
    isHermitian_sum_expectation (μ := μ) hherm
  exact trace_exp_monotone hcgfHerm (isHermitian_real_smul hEsumHerm _)
    hsum_le

/-- **Book §7.6, displays (7.6.2)** (C7-37): the expected-trace chain
`𝔼 tr(e^{θY} − I) ≤ tr(e^{g(θ)𝔼Y} − I) ≤ tr(e^{g(θ)M} − I) =
tr φ(g(θ)M) ≤ intdim(M)·φ(g(θ)‖M‖) ≤ intdim(M)·e^{g(θ)‖M‖}` — the
monotonicity of the trace exponential, the intrinsic dimension lemma, the
scale invariance of the intrinsic dimension, and `φ(a) ≤ e^a`.  Implicit
source displays.

**Author note.** This pointwise-support form is retained for compatibility;
see `chernoff_expected_trace_bound_ae` for the source-faithful almost-sure
counterpart. -/
lemma chernoff_expected_trace_bound
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L)
    (hindep : ProbabilityTheory.iIndepFun X μ) (hL : 0 < L)
    {θ : ℝ} (hθ : 0 < θ) (hMpsd : M.PosSemidef)
    (hM : (∑ k, expectation μ (X k)) ≤ M) :
    ∫ ω, (((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
        (Fintype.card n : ℝ)) ∂μ ≤
      intdim M * Real.exp (gChernoff θ L * ‖M‖) := by
  have hgpos : 0 < gChernoff θ L := by
    rw [gChernoff]
    have h2 : (1 : ℝ) < Real.exp (θ * L) := by
      nlinarith [Real.add_one_lt_exp (ne_of_gt (mul_pos hθ hL))]
    exact div_pos (by linarith) hL
  have hYmeas : Measurable fun ω => ∑ k, X k ω :=
    measurable_matsum Finset.univ hmeas
  have hbd : ∀ k ω, ‖X k ω‖ ≤ L := fun k ω =>
    l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
  have hYherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ (Fintype.card ι : ℝ) * L := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
      _ ≤ ∑ _k : ι, L := Finset.sum_le_sum fun k _ => hbd k ω
      _ = (Fintype.card ι : ℝ) * L := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hθYherm : ∀ ω, (θ • ∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hYherm ω) θ
  have hint : Integrable
      (fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re) μ :=
    integrable_trace_exp_re (μ := μ) (hYmeas.const_smul θ) hθYherm
      (norm_smul_le_of_bound hYbd)
  rw [integral_sub hint (integrable_const _), integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have h1 := chernoff_trace_mgf_bound hmeas hherm hmin hmax hindep hL θ
  have hEsumHerm : (∑ k, expectation μ (X k)).IsHermitian :=
    isHermitian_sum_expectation (μ := μ) hherm
  have hgE : (gChernoff θ L • ∑ k, expectation μ (X k)) ≤
      gChernoff θ L • M := by
    rw [Matrix.le_iff, ← smul_sub]
    exact posSemidef_smul_nonneg (Matrix.le_iff.mp hM) hgpos.le
  have h2 := trace_exp_monotone (isHermitian_real_smul hEsumHerm _)
    (isHermitian_real_smul hMpsd.1 _) hgE
  have hgMpsd : (gChernoff θ L • M).PosSemidef :=
    posSemidef_smul_nonneg hMpsd hgpos.le
  have h3 := trace_exp_sub_card_le_intdim_exp hgMpsd
  have h4 : intdim (gChernoff θ L • M) = intdim M := intdim_smul hgpos M
  have h5 : ‖gChernoff θ L • M‖ = gChernoff θ L * ‖M‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hgpos]
  rw [h4, h5] at h3
  linarith [h1, h2, h3]

end TraceMgf

section MainTheorem

/-- **Book Theorem 7.2.1, equation (7.2.2)**:

`P(λ_max(Y) ≥ (1+ε)μ_max) ≤ 2d·[e^ε/(1+ε)^{1+ε}]^{μ_max/L}`
for `ε ≥ L/μ_max`,

with `d = intdim(M)`, `μ_max = λ_max(M)`, and `M ≽ 𝔼Y` a psd upper bound.
Explicit source declaration; §7.6 proof (generalized Laplace transform with
`ψ₁`, intrinsic dimension lemma, `θ = L⁻¹ log(1+ε)`).

**Author note.** Lean makes the source's nondegeneracy assumptions `M ≠ 0` and
`0 < L` explicit because the intrinsic dimension and displayed ratios otherwise
degenerate.  See `intdim_chernoff_tail_ae` for the source-faithful almost-sure
spectral-support counterpart. -/
theorem intdim_chernoff_tail
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L)
    (hindep : ProbabilityTheory.iIndepFun X μ) (hL : 0 < L)
    (hMpsd : M.PosSemidef) (hM0 : M ≠ 0)
    (hM : (∑ k, expectation μ (X k)) ≤ M)
    {ε : ℝ} (hε : L / lambdaMax hMpsd.1 ≤ ε) :
    μ.real {ω | (1 + ε) * lambdaMax hMpsd.1 ≤
        lambdaMax (isHermitian_matsum Finset.univ fun k => hherm k ω)} ≤
      2 * intdim M *
        (Real.exp ε / (1 + ε) ^ (1 + ε)) ^ (lambdaMax hMpsd.1 / L) := by
  classical
  set μmax : ℝ := lambdaMax hMpsd.1 with hmudef
  have hnorm : ‖M‖ = μmax := posSemidef_l2_opNorm_eq_lambdaMax hMpsd
  have hμpos : 0 < μmax := by
    rw [← hnorm]
    exact norm_pos_iff.mpr hM0
  have hεpos : 0 < ε := lt_of_lt_of_le (div_pos hL hμpos) hε
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  have hlogpos : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  set θ : ℝ := Real.log (1 + ε) / L with hθdef
  have hθpos : 0 < θ := div_pos hlogpos hL
  set t : ℝ := (1 + ε) * μmax with htdef
  have htpos : 0 < t := mul_pos h1ε hμpos
  -- the sum is psd and uniformly bounded
  have hpsd : ∀ ω, (∑ k, X k ω).PosSemidef := fun ω =>
    posSemidef_matsum Finset.univ fun k =>
      posSemidef_of_lambdaMin_nonneg (hherm k ω) (hmin k ω)
  have hbd : ∀ k ω, ‖X k ω‖ ≤ L := fun k ω =>
    l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
  have hYmeas : Measurable fun ω => ∑ k, X k ω :=
    measurable_matsum Finset.univ hmeas
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ (Fintype.card ι : ℝ) * L := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
      _ ≤ ∑ _k : ι, L := Finset.sum_le_sum fun k _ => hbd k ω
      _ = (Fintype.card ι : ℝ) * L := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- (7.6.1): generalized Laplace transform with ψ₁
  have h1 := intdim_laplace_psd (μ := μ) (Y := fun ω => ∑ k, X k ω) hYmeas
    hpsd hYbd htpos hθpos
  -- (7.6.2): expected trace bound
  have h2 := chernoff_expected_trace_bound hmeas hherm hmin hmax hindep hL
    hθpos hMpsd hM
  have hexppos : 0 < Real.exp (θ * t) - 1 := by
    nlinarith [Real.add_one_lt_exp (ne_of_gt (mul_pos hθpos htpos))]
  have h3 : μ.real {ω | t ≤
      lambdaMax (isHermitian_matsum Finset.univ fun k => hherm k ω)} ≤
      (Real.exp (θ * t) - 1)⁻¹ *
        (intdim M * Real.exp (gChernoff θ L * ‖M‖)) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hexppos.le))
  -- `θt ≥ 1` from `(1+ε)log(1+ε) ≥ ε ≥ L/μ_max`
  have hθt1 : 1 ≤ θ * t := by
    have h4 := self_le_add_one_mul_log hεpos.le
    have h6 : L / μmax ≤ (1 + ε) * Real.log (1 + ε) := hε.trans h4
    have h7 : L ≤ (1 + ε) * Real.log (1 + ε) * μmax :=
      (div_le_iff₀ hμpos).mp h6
    rw [hθdef, htdef, div_mul_eq_mul_div, le_div_iff₀ hL, one_mul]
    refine h7.trans (le_of_eq (by ring))
  -- the fraction control (7.6.2.5): `(e^{θt}−1)⁻¹ ≤ 2e^{−θt}`
  have hfrac : (Real.exp (θ * t) - 1)⁻¹ ≤ 2 * Real.exp (-(θ * t)) := by
    have h8 := exp_div_exp_sub_one_le (mul_pos hθpos htpos)
    have h9 : 1 + 1 / (θ * t) ≤ 2 := by
      have h10 : 1 / (θ * t) ≤ 1 := by
        rw [div_le_one (mul_pos hθpos htpos)]
        exact hθt1
      linarith
    have h11 : (Real.exp (θ * t) - 1)⁻¹ =
        Real.exp (-(θ * t)) * (Real.exp (θ * t) / (Real.exp (θ * t) - 1)) := by
      rw [Real.exp_neg]
      field_simp
    rw [h11]
    calc Real.exp (-(θ * t)) * (Real.exp (θ * t) / (Real.exp (θ * t) - 1))
        ≤ Real.exp (-(θ * t)) * 2 :=
          mul_le_mul_of_nonneg_left (h8.trans h9) (Real.exp_pos _).le
      _ = 2 * Real.exp (-(θ * t)) := by ring
  -- `g(θ) = ε/L` at the optimal `θ = L⁻¹log(1+ε)`
  have hgval : gChernoff θ L = ε / L := by
    rw [gChernoff, hθdef, div_mul_cancel₀ _ (ne_of_gt hL), Real.exp_log h1ε]
    ring_nf
  refine h3.trans ?_
  rw [hnorm, hgval]
  have hd0 : 0 ≤ intdim M := intdim_nonneg hMpsd
  calc (Real.exp (θ * t) - 1)⁻¹ * (intdim M * Real.exp (ε / L * μmax))
      ≤ 2 * Real.exp (-(θ * t)) * (intdim M * Real.exp (ε / L * μmax)) :=
        mul_le_mul_of_nonneg_right hfrac
          (mul_nonneg hd0 (Real.exp_pos _).le)
    _ = 2 * intdim M * (Real.exp (-(θ * t)) * Real.exp (ε / L * μmax)) := by
        ring
    _ = 2 * intdim M * (Real.exp ε / (1 + ε) ^ (1 + ε)) ^ (μmax / L) := by
        rw [← Real.exp_add,
          Real.rpow_def_of_pos (div_pos (Real.exp_pos _)
            (Real.rpow_pos_of_pos h1ε _)),
          Real.log_div (Real.exp_pos _).ne'
            (Real.rpow_pos_of_pos h1ε _).ne',
          Real.log_exp, Real.log_rpow h1ε, hθdef, htdef]
        congr 1
        field_simp
        ring

/-- **Book Theorem 7.2.1, equation (7.2.1)**:

`𝔼 λ_max(Y) ≤ ((e^θ − 1)/θ)·μ_max + (1/θ)·L·log(2d)` for `θ > 0`,

with `d = intdim(M)`, `μ_max = λ_max(M)`, `M ≽ 𝔼Y` psd.  Explicit source
declaration; §7.6 proof: the functional inverse `ψ⁻¹(u) = θ⁻¹ log(1+u)` of
`ψ₁`, Jensen's inequality for the (concave, increasing) logarithm, the
expected-trace bound, `1 ≤ d·e^{g·μ_max}`, and the change of variables
`θ ↦ θ/L`.

**Author note.** Lean makes the source's nondegeneracy assumptions `M ≠ 0` and
`0 < L` explicit because the intrinsic dimension and displayed ratios otherwise
degenerate.  See `intdim_chernoff_expectation_ae` for the source-faithful
almost-sure spectral-support counterpart. -/
theorem intdim_chernoff_expectation
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L)
    (hindep : ProbabilityTheory.iIndepFun X μ) (hL : 0 < L)
    (hMpsd : M.PosSemidef) (hM0 : M ≠ 0)
    (hM : (∑ k, expectation μ (X k)) ≤ M) {θ : ℝ} (hθ : 0 < θ) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ fun k => hherm k ω) ∂μ ≤
      (Real.exp θ - 1) / θ * lambdaMax hMpsd.1 +
        L * Real.log (2 * intdim M) / θ := by
  classical
  set θ' : ℝ := θ / L with hθ'def
  have hθ'pos : 0 < θ' := div_pos hθ hL
  have hnorm : ‖M‖ = lambdaMax hMpsd.1 := posSemidef_l2_opNorm_eq_lambdaMax hMpsd
  have hμ0 : 0 ≤ ‖M‖ := norm_nonneg M
  have hd1 : 1 ≤ intdim M := one_le_intdim hMpsd hM0
  have hpsd : ∀ ω, (∑ k, X k ω).PosSemidef := fun ω =>
    posSemidef_matsum Finset.univ fun k =>
      posSemidef_of_lambdaMin_nonneg (hherm k ω) (hmin k ω)
  have hbd : ∀ k ω, ‖X k ω‖ ≤ L := fun k ω =>
    l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
  have hYmeas : Measurable fun ω => ∑ k, X k ω :=
    measurable_matsum Finset.univ hmeas
  have hYherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  set R : ℝ := (Fintype.card ι : ℝ) * L with hRdef
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ R := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
      _ ≤ ∑ _k : ι, L := Finset.sum_le_sum fun k _ => hbd k ω
      _ = R := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hRdef]
  have hWpsd : ∀ ω, (θ' • ∑ k, X k ω).PosSemidef := fun ω =>
    posSemidef_smul_nonneg (hpsd ω) hθ'pos.le
  have hWherm : ∀ ω, (θ' • ∑ k, X k ω).IsHermitian := fun ω => (hWpsd ω).1
  have hWbd : ∀ ω, ‖θ' • ∑ k, X k ω‖ ≤ θ' * R := fun ω => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ'pos]
    exact mul_le_mul_of_nonneg_left (hYbd ω) hθ'pos.le
  -- the auxiliary random variable `Z = 1 + (tr e^{θ'Y} − d)`
  set Z : Ω → ℝ := fun ω =>
    1 + (((NormedSpace.exp (θ' • ∑ k, X k ω)).trace).re -
      (Fintype.card n : ℝ)) with hZdef
  have hZlow : ∀ ω, 1 ≤ Z ω := by
    intro ω
    have h1 : (Fintype.card n : ℝ) ≤
        ((NormedSpace.exp (θ' • ∑ k, X k ω)).trace).re := by
      rw [trace_exp_re_eq_sum (hWherm ω)]
      calc (Fintype.card n : ℝ) = ∑ _i : n, (1 : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        _ ≤ ∑ i, Real.exp ((hWherm ω).eigenvalues i) :=
            Finset.sum_le_sum fun i _ =>
              Real.one_le_exp ((hWpsd ω).eigenvalues_nonneg i)
    simp only [hZdef]
    linarith
  have hZhigh : ∀ ω, Z ω ≤ 1 + (Fintype.card n : ℝ) * Real.exp (θ' * R) := by
    intro ω
    have h1 := trace_re_le_card_mul_lambdaMax (isHermitian_exp (hWherm ω))
    rw [lambdaMax_exp (hWherm ω)] at h1
    have h2 : lambdaMax (hWherm ω) ≤ θ' * R := by
      rw [← posSemidef_l2_opNorm_eq_lambdaMax (hWpsd ω)]
      exact hWbd ω
    have h3 : ((NormedSpace.exp (θ' • ∑ k, X k ω)).trace).re ≤
        (Fintype.card n : ℝ) * Real.exp (θ' * R) :=
      h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2)
        (Nat.cast_nonneg _))
    have hcard : (0 : ℝ) ≤ (Fintype.card n : ℝ) := Nat.cast_nonneg _
    simp only [hZdef]
    linarith
  -- pointwise: `λ_max(Y) ≤ θ'⁻¹ log Z` (the ψ⁻¹ identity of (7.6.4))
  have hpoint : ∀ ω, lambdaMax (hYherm ω) ≤ θ'⁻¹ * Real.log (Z ω) := by
    intro ω
    obtain ⟨i₀, hi₀⟩ := exists_eigenvalues_eq_lambdaMax (hWherm ω)
    have hcard1 : 1 ≤ Fintype.card n := Fintype.card_pos
    have h2 : Real.exp (lambdaMax (hWherm ω)) + ((Fintype.card n : ℝ) - 1) ≤
        ((NormedSpace.exp (θ' • ∑ k, X k ω)).trace).re := by
      rw [trace_exp_re_eq_sum (hWherm ω)]
      have h3 := Finset.add_sum_erase Finset.univ
        (fun i => Real.exp ((hWherm ω).eigenvalues i)) (Finset.mem_univ i₀)
      have h4 : ((Fintype.card n : ℝ) - 1) ≤
          ∑ i ∈ Finset.univ.erase i₀,
            Real.exp ((hWherm ω).eigenvalues i) := by
        calc ((Fintype.card n : ℝ) - 1) =
            ∑ _i ∈ Finset.univ.erase i₀, (1 : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one,
                Finset.card_erase_of_mem (Finset.mem_univ i₀),
                Finset.card_univ, Nat.cast_sub hcard1, Nat.cast_one]
          _ ≤ _ := Finset.sum_le_sum fun i _ =>
              Real.one_le_exp ((hWpsd ω).eigenvalues_nonneg i)
      rw [← hi₀]
      linarith [h3, h4]
    have h5 : Real.exp (lambdaMax (hWherm ω)) ≤ Z ω := by
      simp only [hZdef]
      linarith
    have h6 : lambdaMax (hWherm ω) ≤ Real.log (Z ω) := by
      rw [← Real.log_exp (lambdaMax (hWherm ω))]
      exact Real.log_le_log (Real.exp_pos _) h5
    have h7 : lambdaMax (hWherm ω) = θ' * lambdaMax (hYherm ω) :=
      lambdaMax_smul_nonneg (hYherm ω) hθ'pos.le (hWherm ω)
    rw [h7] at h6
    calc lambdaMax (hYherm ω) = θ'⁻¹ * (θ' * lambdaMax (hYherm ω)) := by
          field_simp
      _ ≤ θ'⁻¹ * Real.log (Z ω) :=
          mul_le_mul_of_nonneg_left h6 (inv_nonneg.mpr hθ'pos.le)
  -- integrate and apply Jensen for the logarithm
  have hZmeas : Measurable Z := by
    have h1 : Measurable
        (fun ω => ((NormedSpace.exp (θ' • ∑ k, X k ω)).trace).re) :=
      measurable_trace_exp_re (hYmeas.const_smul θ')
    exact (h1.sub_const _).const_add 1
  have hlamint : Integrable
      (fun ω => lambdaMax (hYherm ω)) μ :=
    integrable_lambdaMax (μ := μ) hYmeas hYherm hYbd
  have hlogint : Integrable (fun ω => θ'⁻¹ * Real.log (Z ω)) μ := by
    refine (Integrable.const_mul ?_ _)
    refine Integrable.of_bound
      ((Real.measurable_log.comp hZmeas).aestronglyMeasurable)
      (max |Real.log 1| |Real.log (1 + (Fintype.card n : ℝ) *
        Real.exp (θ' * R))|) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have hz1 : (0 : ℝ) < 1 := one_pos
    have h1 : Real.log 1 ≤ Real.log (Z ω) :=
      Real.log_le_log hz1 (hZlow ω)
    have h2 : Real.log (Z ω) ≤
        Real.log (1 + (Fintype.card n : ℝ) * Real.exp (θ' * R)) :=
      Real.log_le_log (lt_of_lt_of_le hz1 (hZlow ω)) (hZhigh ω)
    rcases abs_cases (Real.log (Z ω)) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq]
      exact le_max_of_le_right (h2.trans (le_abs_self _))
    · rw [heq]
      refine le_max_of_le_left ?_
      rw [Real.log_one] at h1 ⊢
      rw [abs_zero]
      linarith
  have hElam : ∫ ω, lambdaMax (hYherm ω) ∂μ ≤
      ∫ ω, θ'⁻¹ * Real.log (Z ω) ∂μ :=
    integral_mono hlamint hlogint hpoint
  rw [integral_const_mul] at hElam
  have hjensen := integral_log_le_log_integral (μ := μ) (c := 1)
    (C := 1 + (Fintype.card n : ℝ) * Real.exp (θ' * R)) one_pos hZmeas
    hZlow hZhigh
  -- `𝔼Z = 1 + 𝔼(tr − d) ≤ 1 + d·e^{g(θ')‖M‖} ≤ 2d·e^{g(θ')‖M‖}`
  have hθ'Yherm : ∀ ω, (θ' • ∑ k, X k ω).IsHermitian := hWherm
  have hinttr : Integrable
      (fun ω => ((NormedSpace.exp (θ' • ∑ k, X k ω)).trace).re) μ :=
    integrable_trace_exp_re (μ := μ) (hYmeas.const_smul θ') hθ'Yherm hWbd
  have hsubint : Integrable (fun ω =>
      ((NormedSpace.exp (θ' • ∑ k, X k ω)).trace).re -
        (Fintype.card n : ℝ)) μ := hinttr.sub (integrable_const _)
  have hZint : Integrable Z μ := by
    simp only [hZdef]
    exact (integrable_const _).add hsubint
  have hEZ : ∫ ω, Z ω ∂μ = 1 +
      ∫ ω, (((NormedSpace.exp (θ' • ∑ k, X k ω)).trace).re -
        (Fintype.card n : ℝ)) ∂μ := by
    simp only [hZdef]
    rw [integral_add (integrable_const _) hsubint, integral_const]
    simp
  have htr := chernoff_expected_trace_bound hmeas hherm hmin hmax hindep hL
    hθ'pos hMpsd hM
  have hgnn : 0 ≤ gChernoff θ' L := by
    rw [gChernoff]
    have h2 : (1 : ℝ) ≤ Real.exp (θ' * L) :=
      Real.one_le_exp (by positivity)
    have h3 : (0 : ℝ) ≤ Real.exp (θ' * L) - 1 := by linarith
    positivity
  have hone_le : 1 ≤ intdim M * Real.exp (gChernoff θ' L * ‖M‖) := by
    have h1 : (1 : ℝ) ≤ Real.exp (gChernoff θ' L * ‖M‖) :=
      Real.one_le_exp (mul_nonneg hgnn hμ0)
    nlinarith [hd1, h1]
  have hEZle : ∫ ω, Z ω ∂μ ≤
      2 * intdim M * Real.exp (gChernoff θ' L * ‖M‖) := by
    rw [hEZ]
    nlinarith [htr, hone_le]
  have hEZpos : 0 < ∫ ω, Z ω ∂μ := by
    have h1 : (∫ _ω, (1 : ℝ) ∂μ) ≤ ∫ ω, Z ω ∂μ :=
      integral_mono (integrable_const _) hZint hZlow
    simp at h1
    linarith
  have hlogle : Real.log (∫ ω, Z ω ∂μ) ≤
      Real.log (2 * intdim M) + gChernoff θ' L * ‖M‖ := by
    calc Real.log (∫ ω, Z ω ∂μ)
        ≤ Real.log (2 * intdim M * Real.exp (gChernoff θ' L * ‖M‖)) :=
          Real.log_le_log hEZpos hEZle
      _ = Real.log (2 * intdim M) + gChernoff θ' L * ‖M‖ := by
          rw [Real.log_mul (by nlinarith [hd1]) (Real.exp_pos _).ne',
            Real.log_exp]
  -- assemble and change variables `θ' = θ/L`
  have hfinal : ∫ ω, lambdaMax (hYherm ω) ∂μ ≤
      θ'⁻¹ * (Real.log (2 * intdim M) + gChernoff θ' L * ‖M‖) := by
    refine hElam.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hθ'pos.le)
    exact hjensen.trans hlogle
  refine hfinal.trans (le_of_eq ?_)
  have hθ'L : θ' * L = θ := by
    rw [hθ'def, div_mul_cancel₀ _ (ne_of_gt hL)]
  rw [gChernoff, hθ'L, hnorm, hθ'def]
  field_simp
  ring

end MainTheorem

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# Example: a random column submatrix (Tropp §7.2.2)

The §7.2.2 example revisits the random column submatrix of §5.2.1 with the
intrinsic Chernoff bound: for `Z = Σ_k δ_k b_{:k}e_k*` (Bernoulli(q) column
sampling from a fixed `m × n` matrix `B`, realized by the Chapter-5 model
`columnSubmatrix`) and `Y = ZZ* = Σ_k δ_k b_{:k}b_{:k}*`:

* `M = 𝔼Y = q·BB*` — Chapter 5's `expectation_column_gram` (C7-10);
* `d = intdim(M) = intdim(BB*) = srank(B)` — scale invariance + the Gram
  identity (C7-11, file 01);
* `λ_max(M) = q·‖B‖²` (C7-12) and `L = max_k ‖b_{:k}‖²` (C7-13, Chapter 5's
  `column_family_bounds`);
* the final display (C7-14), from (7.2.1) at `θ = 1` and `e − 1 ≤ 1.72`:

`𝔼‖Z‖² ≤ 1.72·q·‖B‖² + log(2·srank(B))·max_k ‖b_{:k}‖²`
(`intdim_column_submatrix_upper`).

The hypotheses `B ≠ 0` and `0 < q` make `M ≠ 0` and `L > 0`
(the book's implicit assumptions — with `B = 0` or `q = 0` the model is
trivial and `intdim(M)`/`log` degenerate).

-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [Nonempty m] [Nonempty n]
variable [IsProbabilityMeasure μ]

/-- Lean implementation helper: for `B ≠ 0` the maximum squared column norm
is positive (the positivity of the §7.2.2 parameter `L`). -/
lemma sup_colNormSq_pos {B : Matrix m n ℂ} (hB : B ≠ 0) :
    0 < Finset.univ.sup' Finset.univ_nonempty (colNormSq B) := by
  have hex : ∃ i k, B i k ≠ 0 := by
    by_contra h
    push Not at h
    exact hB (by
      ext i k
      exact h i k)
  obtain ⟨i, k, hik⟩ := hex
  have h1 : 0 < colNormSq B k := by
    have h2 : 0 < ‖B i k‖ ^ 2 := by positivity
    have h3 : ‖B i k‖ ^ 2 ≤ ∑ j, ‖B j k‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖B j k‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have h4 : colNormSq B k = ∑ j, ‖B j k‖ ^ 2 := rfl
    rw [h4]
    linarith
  exact lt_of_lt_of_le h1 (Finset.le_sup' _ (Finset.mem_univ k))

/-- Lean implementation helper: `B ≠ 0` makes the mean bound `M = q·BB*`
nonzero (the §7.2.2 nondegeneracy condition). -/
lemma smul_gram_ne_zero {B : Matrix m n ℂ} (hB : B ≠ 0) {q : ℝ}
    (hq0 : 0 < q) : q • (B * Bᴴ) ≠ 0 := by
  intro h
  rcases smul_eq_zero.mp h with h1 | h2
  · exact hq0.ne' h1
  · have h3 : ‖B‖ ^ 2 = 0 := by
      rw [(l2_opNorm_sq_eq B).1, h2, norm_zero]
    have h4 : ‖B‖ = 0 := by
      nlinarith [norm_nonneg B]
    exact hB (norm_eq_zero.mp h4)

/-- **Book §7.2.2, final display** (C7-14):

`𝔼‖Z‖² ≤ 1.72·q·‖B‖² + log(2·srank(B))·max_k ‖b_{:k}‖²`

for the Bernoulli(q) random column submatrix `Z` of a fixed nonzero matrix
`B` — the intrinsic Chernoff expectation bound (7.2.1) at `θ = 1` applied to
`Y = ZZ* = Σ_k δ_k·b_{:k}b_{:k}*` with `M = 𝔼Y = q·BB*`, using
`intdim(M) = srank(B)` (C7-10–C7-13) and `e − 1 ≤ 1.72`.  Explicit source
display ("the new result depends on the logarithm of the stable rank instead
of `log m`").

**Author note.** Lean states `B ≠ 0` and `0 < q` explicitly so that the
intrinsic-dimension and logarithmic parameters are nondegenerate.  See
`intdim_column_submatrix_upper_of_isBernoulli` for the law-only counterpart and
`intdim_column_submatrix_upper_totalized` for a separately labeled Lean
strengthening at the degenerate corners. -/
theorem intdim_column_submatrix_upper (B : Matrix m n ℂ) (hB : B ≠ 0)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 < q) {δ : n → Ω → ℝ}
    (hmeas : ∀ k, Measurable (δ k)) (hlaw : ∀ k, IsBernoulli q (δ k) μ)
    (hrange : ∀ k ω, δ k ω = 0 ∨ δ k ω = 1)
    (hind : ProbabilityTheory.iIndepFun δ μ) :
    ∫ ω, ‖columnSubmatrix B δ ω‖ ^ 2 ∂μ ≤
      1.72 * (q * ‖B‖ ^ 2) +
        Real.log (2 * stableRank B) *
          Finset.univ.sup' Finset.univ_nonempty (colNormSq B) := by
  classical
  set X : n → Ω → Matrix m m ℂ := fun k ω => δ k ω • colGram B k with hXdef
  have hherm : ∀ (k : n) ω, (X k ω).IsHermitian := fun k ω =>
    isHermitian_real_smul (posSemidef_colGram B k).1 _
  obtain ⟨hmin, hmax⟩ := column_family_bounds B hrange hherm
  have hXmeas : ∀ k, Measurable (X k) := fun k => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => δ k ω • colGram B k i j
    exact (hmeas k).smul_const _
  have hXind : ProbabilityTheory.iIndepFun X μ := by
    refine hind.comp (fun k s => s • colGram B k) fun k => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun s : ℝ => s • colGram B k i j
    exact measurable_id.smul_const _
  have hL : 0 < Finset.univ.sup' Finset.univ_nonempty (colNormSq B) :=
    sup_colNormSq_pos hB
  -- the mean bound `M = q·BB*`
  have hMpsd : (q • (B * Bᴴ)).PosSemidef :=
    posSemidef_smul_nonneg (Matrix.posSemidef_self_mul_conjTranspose B) hq.1
  have hM0 : q • (B * Bᴴ) ≠ 0 := smul_gram_ne_zero hB hq0
  have hM : (∑ k, expectation μ (X k)) ≤ q • (B * Bᴴ) :=
    le_of_eq (expectation_column_gram B hq hmeas hlaw)
  -- the intrinsic Chernoff expectation bound at `θ = 1`
  have h := intdim_chernoff_expectation (μ := μ) hXmeas hherm hmin hmax hXind
    hL hMpsd hM0 hM (θ := 1) one_pos
  -- transport the integrand to `‖Z‖²`
  have hintegrand : (fun ω => ‖columnSubmatrix B δ ω‖ ^ 2) =
      fun ω => lambdaMax (isHermitian_matsum Finset.univ
        fun k => hherm k ω) := by
    funext ω
    rw [sq_norm_eq_lambdaMax_gram]
    exact lambdaMax_congr (columnSubmatrix_gram B hrange ω) _ _
  rw [hintegrand]
  refine h.trans ?_
  -- identify the parameters
  have hmu : lambdaMax hMpsd.1 = q * ‖B‖ ^ 2 := by
    have h1 : lambdaMax hMpsd.1 = q *
        lambdaMax (Matrix.isHermitian_mul_conjTranspose_self B) :=
      lambdaMax_smul_nonneg (Matrix.isHermitian_mul_conjTranspose_self B)
        hq.1 hMpsd.1
    rw [h1, ← sq_norm_eq_lambdaMax_gram]
  have hd : intdim (q • (B * Bᴴ)) = stableRank B := by
    rw [intdim_smul hq0, intdim_gram_eq_stableRank]
  rw [hmu, hd, div_one, div_one]
  have hconst : Real.exp 1 - 1 ≤ 1.72 := const_upper_bound
  have hqB : 0 ≤ q * ‖B‖ ^ 2 := by positivity
  have hlog : 0 ≤ Real.log (2 * stableRank B) := by
    refine Real.log_nonneg ?_
    have h1 := one_le_stableRank hB
    linarith
  nlinarith [hL, hconst, hqB]

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Intrinsic Bernstein, Hermitian case: Theorem 7.7.1 (Tropp §7.7.1)

**Book Theorem 7.7.1 (Matrix Bernstein: Hermitian Case with Intrinsic
Dimension)**: for independent random Hermitian matrices with
`𝔼X_k = 0` and `λ_max(X_k) ≤ L`, `Y = Σ X_k`, a psd upper bound
`V ≽ mVar(Y) = Σ 𝔼X_k²`, `d = intdim(V)`, `v = ‖V‖`:

`P(λ_max(Y) ≥ t) ≤ 4d·exp(−t²/2/(v + Lt/3))` for `t ≥ √v + L/3`
(`intdim_bernstein_herm_tail`).

Proof per §7.7.1: the `ψ₂`-specialization of the generalized Laplace
transform bound (`intdim_laplace_psiTwo`, file 02; the cancellation
`𝔼 tr Y = 0` happens here), the Bernstein trace-mgf bound
`𝔼 tr e^{θY} ≤ tr exp(g(θ)·𝔼Y²)` (`bernstein_trace_mgf_bound`, C7-45 —
the printed `g(θ) = exp((θ²/2)/(1−θL/3))` has a spurious `exp`; the
correct `g` is Lemma 6.6.2's `gBernstein`), the
intrinsic dimension lemma (file 03), the fraction control
`e^a/(e^a−a−1) ≤ 1 + 3/a²` (file 02, from the book's "numerical fact"),
the choice `θ = t/(v + Lt/3)` with its exponent identity, and the
threshold reduction `t ≥ √v + L/3 ⟹ t² ≥ v + Lt/3`
(`bernstein_threshold_sq`, the book's quadratic-root computation with
`√(a+b) ≤ √a + √b`).

The core estimate `intdim_bernstein_herm_tail_core` is stated under the
nonvacuousness condition `t² ≥ v + Lt/3` itself ("we may as well limit our
attention to the case where `t² ≥ v + Lt/3`") — the form consumed by the
rectangular case (file 07) and by Corollary 7.3.3 (file 09).

Statement conventions: `V ≠ 0` is explicit (`intdim(V)` is a `0/0`
otherwise and the fully degenerate corner `L = v = t = 0` falsifies the
literal statement); `0 ≤ L` explicit (the Chapter-6 convention); the
standing Chapter-3 regularity `‖X_k ω‖ ≤ R k`.

-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {X : ι → Ω → Matrix n n ℂ} {L : ℝ} {R : ι → ℝ} {V : Matrix n n ℂ}

section TraceMgf

/-- **Book §7.7.1, second display of the proof** (C7-45): "Examining the
proof of the original matrix Bernstein bound for Hermitian matrices, we see
that `𝔼 tr e^{θY} ≤ tr exp(g(θ)·𝔼Y²)`" for `0 < θ`, `θL < 3`.

**Author note.** The printed `g(θ) = exp((θ²/2)/(1−θL/3))` has a spurious
outer exponential.  The substitution below produces the stated exponent with
Lemma 6.6.2's `g(θ) = (θ²/2)/(1−θL/3) = gBernstein`, which is used here.  This
pointwise, two-sided-regularity form is retained for compatibility; see
`bernstein_trace_mgf_bound_one_sided` for the source-faithful one-sided/a.e.
counterpart. -/
lemma bernstein_trace_mgf_bound
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hbd : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L)
    (hindep : ProbabilityTheory.iIndepFun X μ)
    {θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) :
    ∫ ω, ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re ∂μ ≤
      ((NormedSpace.exp (gBernstein θ L •
        ∑ k, expectation μ (fun ω => X k ω * X k ω))).trace).re := by
  have h1 := trace_exp_sum_le_trace_exp_sum_cgf (μ := μ) hmeas hherm hbd
    hindep θ
  have hrw : (fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re) =
      fun ω => ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re := by
    funext ω
    rw [Finset.smul_sum]
  rw [hrw]
  refine h1.trans ?_
  have hcgf_le : ∀ k, matrixCgf μ (X k) θ ≤
      gBernstein θ L • expectation μ (fun ω => X k ω * X k ω) := fun k =>
    bernstein_matrix_cgf_le (μ := μ) (hmeas k) (hherm k) (hbd k) (hcent k)
      (hmax k) hθ hθL
  have hsum_le : (∑ k, matrixCgf μ (X k) θ) ≤
      gBernstein θ L • ∑ k, expectation μ (fun ω => X k ω * X k ω) := by
    rw [Finset.smul_sum]
    exact sum_loewner_mono Finset.univ fun k _ => hcgf_le k
  have hcgfHerm : (∑ k, matrixCgf μ (X k) θ).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => isHermitian_cfc_log _
  have hE2herm : ∀ k, (expectation μ (fun ω => X k ω * X k ω)).IsHermitian :=
    fun k => isHermitian_expectation
      (Filter.Eventually.of_forall fun ω => isHermitian_sq (hherm k ω))
  have hEsumHerm :
      (∑ k, expectation μ (fun ω => X k ω * X k ω)).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => hE2herm k
  exact trace_exp_monotone hcgfHerm (isHermitian_real_smul hEsumHerm _)
    hsum_le

/-- **Book §7.7.1, displays (7.7.2)** (C7-46): the expected-trace chain
`𝔼 tr(e^{θY} − I) ≤ tr(e^{g(θ)𝔼Y²} − I) ≤ tr(e^{g(θ)V} − I) =
tr φ(g(θ)V) ≤ intdim(V)·φ(g(θ)v) ≤ d·e^{g(θ)v}`.  Implicit source
displays.

**Author note.** This pointwise, two-sided-regularity form is retained for
compatibility; see `bernstein_expected_trace_bound_one_sided` for the
source-faithful one-sided/a.e. counterpart. -/
lemma bernstein_expected_trace_bound
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hbd : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L)
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hVpsd : V.PosSemidef)
    (hV : (∑ k, expectation μ (fun ω => X k ω * X k ω)) ≤ V)
    {θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) :
    ∫ ω, (((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
        (Fintype.card n : ℝ)) ∂μ ≤
      intdim V * Real.exp (gBernstein θ L * ‖V‖) := by
  have hgpos : 0 < gBernstein θ L := by
    rw [gBernstein]
    exact div_pos (by positivity) (by linarith)
  have hYmeas : Measurable fun ω => ∑ k, X k ω :=
    measurable_matsum Finset.univ hmeas
  have hYherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ ∑ k, R k := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
      _ ≤ ∑ k, R k := Finset.sum_le_sum fun k _ => hbd k ω
  have hθYherm : ∀ ω, (θ • ∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hYherm ω) θ
  have hint : Integrable
      (fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re) μ :=
    integrable_trace_exp_re (μ := μ) (hYmeas.const_smul θ) hθYherm
      (norm_smul_le_of_bound hYbd)
  rw [integral_sub hint (integrable_const _), integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have h1 := bernstein_trace_mgf_bound hmeas hherm hbd hcent hmax hindep
    hθ hθL
  have hE2herm : ∀ k, (expectation μ (fun ω => X k ω * X k ω)).IsHermitian :=
    fun k => isHermitian_expectation
      (Filter.Eventually.of_forall fun ω => isHermitian_sq (hherm k ω))
  have hEsumHerm :
      (∑ k, expectation μ (fun ω => X k ω * X k ω)).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => hE2herm k
  have hgE : (gBernstein θ L •
      ∑ k, expectation μ (fun ω => X k ω * X k ω)) ≤ gBernstein θ L • V := by
    rw [Matrix.le_iff, ← smul_sub]
    exact posSemidef_smul_nonneg (Matrix.le_iff.mp hV) hgpos.le
  have h2 := trace_exp_monotone (isHermitian_real_smul hEsumHerm _)
    (isHermitian_real_smul hVpsd.1 _) hgE
  have hgVpsd : (gBernstein θ L • V).PosSemidef :=
    posSemidef_smul_nonneg hVpsd hgpos.le
  have h3 := trace_exp_sub_card_le_intdim_exp hgVpsd
  have h4 : intdim (gBernstein θ L • V) = intdim V := intdim_smul hgpos V
  have h5 : ‖gBernstein θ L • V‖ = gBernstein θ L * ‖V‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hgpos]
  rw [h4, h5] at h3
  linarith [h1, h2, h3]

end TraceMgf

section Threshold

/-- **Book §7.7.1, final displays of the proof** (C7-50): the sufficient
condition — "We can simplify the restriction on `t` by solving the quadratic
inequality … `(1/2)[L/3 + √(L²/9 + 4v)] ≤ √v + L/3` … using
`√(a+b) ≤ √a + √b`.  Therefore, the tail bound is valid when
`t ≥ √v + L/3`": `t ≥ √v + L/3` implies `t² ≥ v + Lt/3`.  Explicit source
display chain. -/
lemma bernstein_threshold_sq {v L t : ℝ} (hv : 0 ≤ v) (hL : 0 ≤ L)
    (ht : Real.sqrt v + L / 3 ≤ t) : v + L * t / 3 ≤ t ^ 2 := by
  have h1 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  have h2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
  nlinarith [ht, h1, h2, mul_nonneg h1 hL, sq_nonneg (t - Real.sqrt v)]

end Threshold

section MainTheorem

/-- Lean implementation helper (the "`Y` has zero mean" cancellation of
(7.7.1)): `𝔼 tr Y = 0` for a centered family. -/
lemma integral_trace_re_eq_zero
    (hmeas : ∀ k, Measurable (X k)) (hbd : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hcent : ∀ k, expectation μ (X k) = 0) :
    ∫ ω, ((∑ k, X k ω).trace).re ∂μ = 0 := by
  have h1 : (fun ω => ((∑ k, X k ω).trace).re) =
      fun ω => ∑ k, (((X k ω).trace).re) := by
    funext ω
    rw [Matrix.trace_sum, Complex.re_sum]
  rw [h1, MeasureTheory.integral_finsetSum (μ := μ) Finset.univ
    (f := fun k (ω : Ω) => (((X k ω).trace).re)) fun k _ =>
      integrable_trace_re (hmeas k) (hbd k)]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hint : ∀ i : n, Integrable (fun ω => X k ω i i) μ := fun i =>
    mintegrable_of_norm_bound (hmeas k) (hbd k) i i
  have h2 : (fun ω => (((X k ω).trace).re)) =
      fun ω => ∑ i, ((X k ω) i i).re := by
    funext ω
    rw [Matrix.trace, Complex.re_sum]
    rfl
  rw [h2, MeasureTheory.integral_finsetSum (μ := μ) Finset.univ
    (f := fun i (ω : Ω) => ((X k ω) i i).re) fun i _ => (hint i).re]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h3 : ∫ ω, (X k ω i i).re ∂μ = (∫ ω, X k ω i i ∂μ).re :=
    integral_re (hint i)
  rw [h3, show (∫ ω, X k ω i i ∂μ) = expectation μ (X k) i i from
    (expectation_apply _ _ _).symm, hcent k]
  simp

/-- **Book §7.7.1, displays (7.7.3) and the vacuousness reduction**
(C7-43/C7-48/C7-49), core form: for `t > 0` with `t² ≥ v + Lt/3`,

`P(λ_max(Y) ≥ t) ≤ 4d·exp(−t²/2/(v + Lt/3))`

— the `ψ₂` Laplace-transform bound with `θ = t/(v + Lt/3)`, the fraction
control `1 + 3/(θt)² ≤ 4`, and the exponent identity
`−θt + g(θ)v = −t²/2/(v+Lt/3)`.  This is the statement the book proves
before simplifying the restriction on `t`; it is the form consumed by the
rectangular case and by Corollary 7.3.3.

**Author note.** This pointwise, two-sided-regularity form is retained for
compatibility; see `intdim_bernstein_herm_tail_core_one_sided` for the
source-faithful one-sided/a.e. counterpart. -/
theorem intdim_bernstein_herm_tail_core
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hbd : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hVpsd : V.PosSemidef) (hV0 : V ≠ 0)
    (hV : (∑ k, expectation μ (fun ω => X k ω * X k ω)) ≤ V)
    {t : ℝ} (ht : 0 < t) (htv : ‖V‖ + L * t / 3 ≤ t ^ 2) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        fun k => hherm k ω)} ≤
      4 * intdim V * Real.exp (-(t ^ 2) / 2 / (‖V‖ + L * t / 3)) := by
  classical
  set v : ℝ := ‖V‖ with hvdef
  have hvpos : 0 < v := norm_pos_iff.mpr hV0
  set D : ℝ := v + L * t / 3 with hDdef
  have hDpos : 0 < D := by
    have h1 : 0 ≤ L * t / 3 := by positivity
    simp only [hDdef]
    linarith
  set θ : ℝ := t / D with hθdef
  have hθpos : 0 < θ := div_pos ht hDpos
  have hθL : θ * L < 3 := by
    rw [hθdef, div_mul_eq_mul_div, div_lt_iff₀ hDpos]
    simp only [hDdef]
    nlinarith [hvpos, ht]
  -- the ψ₂-Laplace bound (7.7.1)
  have hYmeas : Measurable fun ω => ∑ k, X k ω :=
    measurable_matsum Finset.univ hmeas
  have hYherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ ∑ k, R k := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
      _ ≤ ∑ k, R k := Finset.sum_le_sum fun k _ => hbd k ω
  have h1 := intdim_laplace_psiTwo (μ := μ) (Y := fun ω => ∑ k, X k ω)
    hYmeas hYherm hYbd ht hθpos
  -- the zero-mean cancellation and the expected-trace bound
  have hθYherm : ∀ ω, (θ • ∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hYherm ω) θ
  have hinttr : Integrable
      (fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re) μ :=
    integrable_trace_exp_re (μ := μ) (hYmeas.const_smul θ) hθYherm
      (norm_smul_le_of_bound hYbd)
  have hinttrY : Integrable (fun ω => ((∑ k, X k ω).trace).re) μ :=
    integrable_trace_re hYmeas hYbd
  have hEtrY : ∫ ω, ((∑ k, X k ω).trace).re ∂μ = 0 :=
    integral_trace_re_eq_zero hmeas hbd hcent
  have hsplit : ∫ ω, (((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
      θ * ((∑ k, X k ω).trace).re - (Fintype.card n : ℝ)) ∂μ =
      ∫ ω, (((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
        (Fintype.card n : ℝ)) ∂μ := by
    have hfun : (fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
        θ * ((∑ k, X k ω).trace).re - (Fintype.card n : ℝ)) =
        fun ω => (((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
          (Fintype.card n : ℝ)) - θ * ((∑ k, X k ω).trace).re := by
      funext ω
      ring
    have hsub1 : Integrable (fun ω =>
        ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
          (Fintype.card n : ℝ)) μ := hinttr.sub (integrable_const _)
    have hsub2 : Integrable
        (fun ω => θ * ((∑ k, X k ω).trace).re) μ := hinttrY.const_mul θ
    rw [hfun, integral_sub hsub1 hsub2, integral_const_mul, hEtrY,
      mul_zero, sub_zero]
  have h2 := bernstein_expected_trace_bound hmeas hherm hbd hcent hmax
    hindep hVpsd hV hθpos hθL
  -- combine
  have hψpos : 0 < Real.exp (θ * t) - θ * t - 1 := by
    have := Real.add_one_lt_exp (ne_of_gt (mul_pos hθpos ht))
    linarith
  have h3 : μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
      fun k => hherm k ω)} ≤
      (Real.exp (θ * t) - θ * t - 1)⁻¹ *
        (intdim V * Real.exp (gBernstein θ L * v)) := by
    refine h1.trans ?_
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hψpos.le)
  -- fraction control: `(e^{θt} − θt − 1)⁻¹ ≤ 4·e^{−θt}` when `θt ≥ 1`
  have hθt : θ * t = t ^ 2 / D := by
    rw [hθdef, div_mul_eq_mul_div, sq]
  have hθt1 : 1 ≤ θ * t := by
    rw [hθt, le_div_iff₀ hDpos, one_mul]
    simpa only [hDdef, hvdef] using htv
  have hfrac : (Real.exp (θ * t) - θ * t - 1)⁻¹ ≤
      4 * Real.exp (-(θ * t)) := by
    have h8 := exp_div_psiTwo_le (mul_pos hθpos ht)
    have h9 : 1 + 3 / (θ * t) ^ 2 ≤ 4 := by
      have h10 : 3 / (θ * t) ^ 2 ≤ 3 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hθt1]
      linarith
    have h11 : (Real.exp (θ * t) - θ * t - 1)⁻¹ =
        Real.exp (-(θ * t)) *
          (Real.exp (θ * t) / (Real.exp (θ * t) - θ * t - 1)) := by
      rw [Real.exp_neg]
      field_simp
    rw [h11]
    calc Real.exp (-(θ * t)) *
        (Real.exp (θ * t) / (Real.exp (θ * t) - θ * t - 1))
        ≤ Real.exp (-(θ * t)) * 4 :=
          mul_le_mul_of_nonneg_left (h8.trans h9) (Real.exp_pos _).le
      _ = 4 * Real.exp (-(θ * t)) := by ring
  -- the exponent identity (7.7.3): `−θt + g(θ)v = −t²/2/D`
  have hexpid : gBernstein θ L * v + -(θ * t) = -(t ^ 2) / 2 / D := by
    have h1mθL : 1 - θ * L / 3 = v / D := by
      rw [hθdef]
      field_simp
      simp only [hDdef]
      ring
    rw [gBernstein, h1mθL, hθdef]
    have hvne : v ≠ 0 := ne_of_gt hvpos
    field_simp
    ring
  refine h3.trans ?_
  have hd0 : 0 ≤ intdim V := intdim_nonneg hVpsd
  calc (Real.exp (θ * t) - θ * t - 1)⁻¹ *
      (intdim V * Real.exp (gBernstein θ L * v))
      ≤ 4 * Real.exp (-(θ * t)) *
        (intdim V * Real.exp (gBernstein θ L * v)) :=
        mul_le_mul_of_nonneg_right hfrac
          (mul_nonneg hd0 (Real.exp_pos _).le)
    _ = 4 * intdim V *
        (Real.exp (gBernstein θ L * v) * Real.exp (-(θ * t))) := by ring
    _ = 4 * intdim V * Real.exp (-(t ^ 2) / 2 / D) := by
        rw [← Real.exp_add, hexpid]

/-- **Book Theorem 7.7.1 (Matrix Bernstein: Hermitian Case with Intrinsic
Dimension)**:

`P(λ_max(Y) ≥ t) ≤ 4d·exp(−t²/2/(v + Lt/3))` for `t ≥ √v + L/3`,

with `d = intdim(V)`, `v = ‖V‖`, `V ≽ mVar(Y) = Σ𝔼X_k²` psd.  Explicit
source declaration; §7.7.1 proof.

**Author note.** Lean makes `V ≠ 0`, `0 ≤ L`, and the standing norm bound
explicit.  These are needed to avoid the zero-variance corner and to supply
the analytic regularity used by the proof.  See
`intdim_bernstein_herm_tail_one_sided` for the source-faithful one-sided/a.e.
counterpart. -/
theorem intdim_bernstein_herm_tail
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hbd : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hVpsd : V.PosSemidef) (hV0 : V ≠ 0)
    (hV : (∑ k, expectation μ (fun ω => X k ω * X k ω)) ≤ V)
    {t : ℝ} (ht : Real.sqrt ‖V‖ + L / 3 ≤ t) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        fun k => hherm k ω)} ≤
      4 * intdim V * Real.exp (-(t ^ 2) / 2 / (‖V‖ + L * t / 3)) := by
  have hvpos : 0 < ‖V‖ := norm_pos_iff.mpr hV0
  have htpos : 0 < t := by
    have h1 : 0 < Real.sqrt ‖V‖ := Real.sqrt_pos.mpr hvpos
    have h2 : 0 ≤ L / 3 := by positivity
    linarith
  exact intdim_bernstein_herm_tail_core hmeas hherm hbd hcent hmax hL hindep
    hVpsd hV0 hV htpos
    (bernstein_threshold_sq (norm_nonneg V) hL ht)

end MainTheorem

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Intrinsic matrix Bernstein: Theorem 7.3.1 (Tropp §7.3, §7.7.2)

**Book Theorem 7.3.1 (Intrinsic Matrix Bernstein)**:
for independent `d₁ × d₂` random matrices with `𝔼S_k = 0`, `‖S_k‖ ≤ L`,
`Z = Σ S_k`, psd upper bounds `V₁ ≽ mVar₁(Z) = Σ𝔼S_kS_k*`,
`V₂ ≽ mVar₂(Z) = Σ𝔼S_k*S_k`, and
`d = intdim(diag(V₁,V₂))`, `v = max{‖V₁‖, ‖V₂‖}`:

`P(‖Z‖ ≥ t) ≤ 4d·exp(−t²/2/(v + Lt/3))` for `t ≥ √v + L/3`
(`intdim_bernstein_rect_tail`).

§7.7.2 proof: apply Theorem 7.7.1 to the Hermitian dilation `Y = H(Z)`,
using `𝔼Y² = diag(mVar₁(Z), mVar₂(Z)) ≼ diag(V₁,V₂)` (the (2.2.10)
computation at the level of sums, C7-52 — `dilation_sum_sq_eq` +
`fromBlocks_diag_loewner`), `λ_max(H(Z)) = ‖Z‖`, and
`‖diag(V₁,V₂)‖ = max{‖V₁‖,‖V₂‖}`.

Also:

* `intdim_bernstein_rect_tail_core` — the nonvacuousness form
  (`t² ≥ v + Lt/3`), consumed by Corollary 7.3.3 (file 09);
* `intdim_bernstein_uncentered_tail` (C7-22) — "we can adapt the result to
  a sum of uncentered, independent, random, bounded matrices … the
  modifications required … are straightforward";
* `intdim_bernstein_rect_tail_ae` — the a.e.-boundedness wrapper (norm
  truncation, the Chapter-6 pattern), consumed by the sampling corollary.

Statement conventions: `¬(V₁ = 0 ∧ V₂ = 0)` is explicit (`d` is a
`0/0` otherwise), `0 ≤ L` explicit.

-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {S : ι → Ω → Matrix m n ℂ} {L : ℝ}
variable {V₁ : Matrix m m ℂ} {V₂ : Matrix n n ℂ}

section BlockHelpers

/-- Lean implementation helper: a block-diagonal matrix vanishes iff both
blocks vanish. -/
lemma fromBlocks_diag_eq_zero_iff {A : Matrix m m ℂ} {D : Matrix n n ℂ} :
    Matrix.fromBlocks A 0 0 D = 0 ↔ A = 0 ∧ D = 0 := by
  constructor
  · intro h
    constructor
    · ext i j
      have h1 := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
      simpa using h1
    · ext i j
      have h1 := congrFun (congrFun h (Sum.inr i)) (Sum.inr j)
      simpa using h1
  · rintro ⟨rfl, rfl⟩
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks]

/-- **Book §7.7.2, display (C7-52)**: the Loewner comparison of block
diagonals, blockwise — "The semidefinite inequality follows from our
assumptions on `V₁` and `V₂`."  Implicit source claim. -/
lemma fromBlocks_diag_loewner {A A' : Matrix m m ℂ} {D D' : Matrix n n ℂ}
    (h1 : A ≤ A') (h2 : D ≤ D') :
    Matrix.fromBlocks A 0 0 D ≤ Matrix.fromBlocks A' 0 0 D' := by
  rw [Matrix.le_iff]
  have hsub : Matrix.fromBlocks A' 0 0 D' - Matrix.fromBlocks A 0 0 D =
      Matrix.fromBlocks (A' - A) 0 0 (D' - D) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.sub_apply]
  rw [hsub]
  exact posSemidef_fromBlocks_diag (Matrix.le_iff.mp h1) (Matrix.le_iff.mp h2)

/-- **Book §7.7.2, first display** (C7-52): the variance of the dilation at
the level of sums — `Σ 𝔼 H(S_k)² = diag(Σ𝔼S_kS_k*, Σ𝔼S_k*S_k)` (the
(2.2.10) computation; the Chapter-6 `dilation_variance_eq` gives its norm).
Implicit source display. -/
lemma dilation_sum_sq_eq (S : ι → Ω → Matrix m n ℂ) :
    (∑ k, expectation μ (fun ω => hermDilation (S k ω) *
        hermDilation (S k ω))) =
      Matrix.fromBlocks
        (∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)) 0 0
        (∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)) := by
  have h1 : ∀ k, expectation μ (fun ω => hermDilation (S k ω) *
      hermDilation (S k ω)) =
      Matrix.fromBlocks (expectation μ (fun ω => S k ω * (S k ω)ᴴ)) 0 0
        (expectation μ (fun ω => (S k ω)ᴴ * S k ω)) := by
    intro k
    rw [show (fun ω => hermDilation (S k ω) * hermDilation (S k ω)) =
      fun ω => Matrix.fromBlocks (S k ω * (S k ω)ᴴ) 0 0 ((S k ω)ᴴ * S k ω)
      from funext fun ω => hermDilation_sq (S k ω)]
    exact expectation_fromBlocks_diag
  rw [Finset.sum_congr rfl fun k _ => h1 k, sum_fromBlocks_diag]

end BlockHelpers

section RectTheorem

variable [Nonempty (m ⊕ n)]

/-- **Book Theorem 7.3.1, core form** (C7-15/C7-51): the intrinsic Bernstein
tail bound under the nonvacuousness condition `t² ≥ v + Lt/3` (the form the
§7.7.1 proof establishes before simplifying the threshold; consumed by
Corollary 7.3.3). -/
theorem intdim_bernstein_rect_tail_core
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k ω, ‖S k ω‖ ≤ L) (hL : 0 ≤ L)
    (hcent : ∀ k, expectation μ (S k) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ)
    (hV₁psd : V₁.PosSemidef) (hV₂psd : V₂.PosSemidef)
    (hV0 : ¬(V₁ = 0 ∧ V₂ = 0))
    (hV₁ : (∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)) ≤ V₁)
    (hV₂ : (∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)) ≤ V₂)
    {t : ℝ} (ht : 0 < t)
    (htv : max ‖V₁‖ ‖V₂‖ + L * t / 3 ≤ t ^ 2) :
    μ.real {ω | t ≤ ‖∑ k, S k ω‖} ≤
      4 * intdim (Matrix.fromBlocks V₁ 0 0 V₂) *
        Real.exp (-(t ^ 2) / 2 / (max ‖V₁‖ ‖V₂‖ + L * t / 3)) := by
  classical
  set Y : ι → Ω → Matrix (m ⊕ n) (m ⊕ n) ℂ :=
    fun k ω => hermDilation (S k ω) with hYdef
  have hYmeas : ∀ k, Measurable (Y k) := fun k =>
    measurable_hermDilation_fun.comp (hmeas k)
  have hYherm : ∀ k ω, (Y k ω).IsHermitian := fun k ω =>
    isHermitian_hermDilation (S k ω)
  have hYbd : ∀ k ω, ‖Y k ω‖ ≤ (fun _ : ι => L) k := fun k ω => by
    show ‖hermDilation (S k ω)‖ ≤ L
    rw [l2_opNorm_hermDilation]
    exact hbd k ω
  have hYcent : ∀ k, expectation μ (Y k) = 0 := fun k => by
    rw [show Y k = fun ω => hermDilation (S k ω) from rfl,
      expectation_hermDilation, hcent k, hermDilation_zero]
  have hYmax : ∀ k ω, lambdaMax (hYherm k ω) ≤ L := fun k ω =>
    ((le_abs_self _).trans (abs_lambdaMax_le _)).trans (hYbd k ω)
  have hYind : ProbabilityTheory.iIndepFun Y μ :=
    hind.comp (fun _ => hermDilation) fun _ => measurable_hermDilation_fun
  -- the block-diagonal variance bound
  set V : Matrix (m ⊕ n) (m ⊕ n) ℂ := Matrix.fromBlocks V₁ 0 0 V₂ with hVdef
  have hVpsd : V.PosSemidef := posSemidef_fromBlocks_diag hV₁psd hV₂psd
  have hV0' : V ≠ 0 := fun h => hV0 (fromBlocks_diag_eq_zero_iff.mp h)
  have hVle : (∑ k, expectation μ (fun ω => Y k ω * Y k ω)) ≤ V := by
    rw [show (fun (k : ι) => expectation μ (fun ω => Y k ω * Y k ω)) =
      fun k => expectation μ (fun ω => hermDilation (S k ω) *
        hermDilation (S k ω)) from rfl, dilation_sum_sq_eq S]
    exact fromBlocks_diag_loewner hV₁ hV₂
  have hVnorm : ‖V‖ = max ‖V₁‖ ‖V₂‖ := l2_opNorm_fromBlocks_diagonal V₁ V₂
  -- the Hermitian core bound
  have htv' : ‖V‖ + L * t / 3 ≤ t ^ 2 := by
    rw [hVnorm]
    exact htv
  have h := intdim_bernstein_herm_tail_core (μ := μ) hYmeas hYherm hYbd
    hYcent hYmax hL hYind hVpsd hV0' hVle ht htv'
  -- the event is `{t ≤ ‖Z‖}` through `λ_max(H(Z)) = ‖Z‖`
  have hevent : {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
      fun k => hYherm k ω)} = {ω | t ≤ ‖∑ k, S k ω‖} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have h1 : (∑ k, Y k ω) = hermDilation (∑ k, S k ω) := by
      rw [show (fun k => Y k ω) = fun k => hermDilation (S k ω) from rfl]
      exact (hermDilation_sum fun k => S k ω).symm
    rw [lambdaMax_congr h1 (isHermitian_matsum Finset.univ
      fun k => hYherm k ω) (isHermitian_hermDilation _),
      lambdaMax_hermDilation]
  rw [hevent, hVnorm] at h
  exact h

/-- **Book Theorem 7.3.1 (Intrinsic Matrix Bernstein)**:

`P(‖Z‖ ≥ t) ≤ 4d·exp(−t²/2/(v + Lt/3))` for `t ≥ √v + L/3`,

with `d = intdim(diag(V₁,V₂))`, `v = max{‖V₁‖,‖V₂‖}`.  Explicit source
declaration; §7.7.2 proof (Theorem 7.7.1 applied to the Hermitian dilation).

**Author note.** Lean explicitly assumes `¬(V₁ = 0 ∧ V₂ = 0)` and `0 ≤ L`
to exclude the degenerate intrinsic-dimension denominator and record the sign
convention used in the proof. -/
theorem intdim_bernstein_rect_tail
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k ω, ‖S k ω‖ ≤ L) (hL : 0 ≤ L)
    (hcent : ∀ k, expectation μ (S k) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ)
    (hV₁psd : V₁.PosSemidef) (hV₂psd : V₂.PosSemidef)
    (hV0 : ¬(V₁ = 0 ∧ V₂ = 0))
    (hV₁ : (∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)) ≤ V₁)
    (hV₂ : (∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)) ≤ V₂)
    {t : ℝ} (ht : Real.sqrt (max ‖V₁‖ ‖V₂‖) + L / 3 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, S k ω‖} ≤
      4 * intdim (Matrix.fromBlocks V₁ 0 0 V₂) *
        Real.exp (-(t ^ 2) / 2 / (max ‖V₁‖ ‖V₂‖ + L * t / 3)) := by
  have hvpos : 0 < max ‖V₁‖ ‖V₂‖ := by
    rcases (not_and_or.mp hV0) with h | h
    · exact lt_max_of_lt_left (norm_pos_iff.mpr h)
    · exact lt_max_of_lt_right (norm_pos_iff.mpr h)
  have htpos : 0 < t := by
    have h1 : 0 < Real.sqrt (max ‖V₁‖ ‖V₂‖) := Real.sqrt_pos.mpr hvpos
    have h2 : 0 ≤ L / 3 := by positivity
    linarith
  exact intdim_bernstein_rect_tail_core hmeas hbd hL hcent hind hV₁psd
    hV₂psd hV0 hV₁ hV₂ htpos
    (bernstein_threshold_sq (le_max_of_le_left (norm_nonneg V₁)) hL ht)

/-- **Book §7.3.1 discussion** (C7-22): "we can adapt the result to a sum of
uncentered, independent, random, bounded matrices … The modifications
required in these cases are straightforward" — the uncentered variant, with
the tail for `Z − 𝔼Z` and the centered variance bounds.  Implicit source
claim, formalized with the Chapter-6 centering pattern.

**Author note.** This pointwise centered-bound form is retained for
compatibility; see `intdim_bernstein_uncentered_tail_ae` for the source-faithful
almost-sure counterpart and `intdim_bernstein_uncentered_expectation` for the
missing expectation conclusion. -/
theorem intdim_bernstein_uncentered_tail
    (hmeas : ∀ k, Measurable (S k))
    (hbd : ∀ k ω, ‖S k ω - expectation μ (S k)‖ ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun S μ)
    (hV₁psd : V₁.PosSemidef) (hV₂psd : V₂.PosSemidef)
    (hV0 : ¬(V₁ = 0 ∧ V₂ = 0))
    (hV₁ : (∑ k, expectation μ (fun ω => (S k ω - expectation μ (S k)) *
      (S k ω - expectation μ (S k))ᴴ)) ≤ V₁)
    (hV₂ : (∑ k, expectation μ (fun ω => (S k ω - expectation μ (S k))ᴴ *
      (S k ω - expectation μ (S k)))) ≤ V₂)
    {t : ℝ} (ht : Real.sqrt (max ‖V₁‖ ‖V₂‖) + L / 3 ≤ t) :
    μ.real {ω | t ≤ ‖(∑ k, S k ω) - ∑ k, expectation μ (S k)‖} ≤
      4 * intdim (Matrix.fromBlocks V₁ 0 0 V₂) *
        Real.exp (-(t ^ 2) / 2 / (max ‖V₁‖ ‖V₂‖ + L * t / 3)) := by
  classical
  set S' : ι → Ω → Matrix m n ℂ :=
    fun k ω => S k ω - expectation μ (S k) with hS'def
  have hmeas' : ∀ k, Measurable (S' k) := fun k =>
    (measurable_sub_const (expectation μ (S k))).comp (hmeas k)
  have hSint : ∀ k, MIntegrable (S k) μ := fun k => by
    refine mintegrable_rect_of_norm_bound (C := L + ‖expectation μ (S k)‖)
      (hmeas k) fun ω => ?_
    calc ‖S k ω‖ = ‖(S k ω - expectation μ (S k)) + expectation μ (S k)‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖S k ω - expectation μ (S k)‖ + ‖expectation μ (S k)‖ :=
        norm_add_le _ _
    _ ≤ L + ‖expectation μ (S k)‖ := by
          have := hbd k ω
          linarith
  have hcent' : ∀ k, expectation μ (S' k) = 0 := by
    intro k
    have hconst : MIntegrable (fun _ : Ω => expectation μ (S k)) μ :=
      mintegrable_rect_of_norm_bound (C := ‖expectation μ (S k)‖)
        measurable_const fun ω => le_refl _
    have hsub := expectation_sub (μ := μ) (hSint k) hconst
    rw [show S' k = fun ω => S k ω - (fun _ : Ω => expectation μ (S k)) ω
      from rfl, hsub, expectation_const (μ := μ), sub_self]
  have hind' : ProbabilityTheory.iIndepFun S' μ :=
    hind.comp (fun k M => M - expectation μ (S k)) fun k =>
      measurable_sub_const _
  have h := intdim_bernstein_rect_tail (μ := μ) hmeas' hbd hL hcent' hind'
    hV₁psd hV₂psd hV0 hV₁ hV₂ ht
  have hsum_eq : (fun ω => ‖∑ k, S' k ω‖) =
      fun ω => ‖(∑ k, S k ω) - ∑ k, expectation μ (S k)‖ := by
    funext ω
    show ‖∑ k, (S k ω - expectation μ (S k))‖ = _
    rw [Finset.sum_sub_distrib]
  rw [show {ω | t ≤ ‖∑ k, S' k ω‖} =
    {ω | t ≤ ‖(∑ k, S k ω) - ∑ k, expectation μ (S k)‖} from by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [congrFun hsum_eq ω]] at h
  exact h

/-- Lean implementation helper: the a.e.-bounded norm-truncation wrapper for
**Book Theorem 7.3.1**, used when independent copies inherit the norm bound
only almost everywhere. -/
theorem intdim_bernstein_rect_tail_ae
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ L)
    (hL : 0 ≤ L) (hcent : ∀ k, expectation μ (S k) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ)
    (hV₁psd : V₁.PosSemidef) (hV₂psd : V₂.PosSemidef)
    (hV0 : ¬(V₁ = 0 ∧ V₂ = 0))
    (hV₁ : (∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)) ≤ V₁)
    (hV₂ : (∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)) ≤ V₂)
    {t : ℝ} (ht : Real.sqrt (max ‖V₁‖ ‖V₂‖) + L / 3 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, S k ω‖} ≤
      4 * intdim (Matrix.fromBlocks V₁ 0 0 V₂) *
        Real.exp (-(t ^ 2) / 2 / (max ‖V₁‖ ‖V₂‖ + L * t / 3)) := by
  classical
  set S' : ι → Ω → Matrix m n ℂ := fun k ω => truncateNorm L (S k ω)
    with hS'def
  have hae : ∀ k, S' k =ᵐ[μ] S k := fun k => (hbd k).mono fun ω h => by
    show truncateNorm L (S k ω) = S k ω
    rw [truncateNorm, if_pos h]
  have hmeas' : ∀ k, Measurable (S' k) := fun k =>
    measurable_truncateNorm.comp (hmeas k)
  have hbd' : ∀ k ω, ‖S' k ω‖ ≤ L := fun k ω => truncateNorm_norm_le hL _
  have hcent' : ∀ k, expectation μ (S' k) = 0 := fun k => by
    rw [expectation_congr_ae (hae k), hcent k]
  have hind' : ProbabilityTheory.iIndepFun S' μ :=
    hind.comp (fun _ => truncateNorm L) fun _ => measurable_truncateNorm
  have hv1 : ∀ k, expectation μ (fun ω => S' k ω * (S' k ω)ᴴ) =
      expectation μ (fun ω => S k ω * (S k ω)ᴴ) := by
    intro k
    refine expectation_congr_ae ((hae k).mono fun ω hω => ?_)
    have h' : S' k ω = S k ω := hω
    show S' k ω * (S' k ω)ᴴ = S k ω * (S k ω)ᴴ
    rw [h']
  have hv2 : ∀ k, expectation μ (fun ω => (S' k ω)ᴴ * S' k ω) =
      expectation μ (fun ω => (S k ω)ᴴ * S k ω) := by
    intro k
    refine expectation_congr_ae ((hae k).mono fun ω hω => ?_)
    have h' : S' k ω = S k ω := hω
    show (S' k ω)ᴴ * S' k ω = (S k ω)ᴴ * S k ω
    rw [h']
  have hV₁' : (∑ k, expectation μ (fun ω => S' k ω * (S' k ω)ᴴ)) ≤ V₁ := by
    rw [Finset.sum_congr rfl fun k _ => hv1 k]
    exact hV₁
  have hV₂' : (∑ k, expectation μ (fun ω => (S' k ω)ᴴ * S' k ω)) ≤ V₂ := by
    rw [Finset.sum_congr rfl fun k _ => hv2 k]
    exact hV₂
  have h := intdim_bernstein_rect_tail (μ := μ) hmeas' hbd' hL hcent' hind'
    hV₁psd hV₂psd hV0 hV₁' hV₂' ht
  have hsum_ae : (fun ω => ∑ k, S' k ω) =ᵐ[μ] fun ω => ∑ k, S k ω := by
    have hall : ∀ᵐ ω ∂μ, ∀ k, S' k ω = S k ω :=
      (MeasureTheory.ae_all_iff).mpr hae
    refine hall.mono fun ω h => ?_
    show (∑ k, S' k ω) = ∑ k, S k ω
    exact Finset.sum_congr rfl fun k _ => h k
  have hmeq : μ {ω | t ≤ ‖∑ k, S' k ω‖} = μ {ω | t ≤ ‖∑ k, S k ω‖} := by
    refine MeasureTheory.measure_congr ?_
    refine hsum_ae.mono fun ω hω => ?_
    have h' : (∑ k, S' k ω) = ∑ k, S k ω := hω
    show (t ≤ ‖∑ k, S' k ω‖) = (t ≤ ‖∑ k, S k ω‖)
    rw [h']
  have hreal : μ.real {ω | t ≤ ‖∑ k, S' k ω‖} =
      μ.real {ω | t ≤ ‖∑ k, S k ω‖} := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, hmeq]
  rw [hreal] at h
  exact h

/-- Lean implementation helper: the a.e.-bounded norm-truncation wrapper for
the core form of **Book Theorem 7.3.1**, used by the nonvacuousness branch of
Corollary 7.3.3. -/
theorem intdim_bernstein_rect_tail_core_ae
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ L)
    (hL : 0 ≤ L) (hcent : ∀ k, expectation μ (S k) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ)
    (hV₁psd : V₁.PosSemidef) (hV₂psd : V₂.PosSemidef)
    (hV0 : ¬(V₁ = 0 ∧ V₂ = 0))
    (hV₁ : (∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)) ≤ V₁)
    (hV₂ : (∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)) ≤ V₂)
    {t : ℝ} (ht : 0 < t)
    (htv : max ‖V₁‖ ‖V₂‖ + L * t / 3 ≤ t ^ 2) :
    μ.real {ω | t ≤ ‖∑ k, S k ω‖} ≤
      4 * intdim (Matrix.fromBlocks V₁ 0 0 V₂) *
        Real.exp (-(t ^ 2) / 2 / (max ‖V₁‖ ‖V₂‖ + L * t / 3)) := by
  classical
  set S' : ι → Ω → Matrix m n ℂ := fun k ω => truncateNorm L (S k ω)
    with hS'def
  have hae : ∀ k, S' k =ᵐ[μ] S k := fun k => (hbd k).mono fun ω h => by
    show truncateNorm L (S k ω) = S k ω
    rw [truncateNorm, if_pos h]
  have hmeas' : ∀ k, Measurable (S' k) := fun k =>
    measurable_truncateNorm.comp (hmeas k)
  have hbd' : ∀ k ω, ‖S' k ω‖ ≤ L := fun k ω => truncateNorm_norm_le hL _
  have hcent' : ∀ k, expectation μ (S' k) = 0 := fun k => by
    rw [expectation_congr_ae (hae k), hcent k]
  have hind' : ProbabilityTheory.iIndepFun S' μ :=
    hind.comp (fun _ => truncateNorm L) fun _ => measurable_truncateNorm
  have hv1 : ∀ k, expectation μ (fun ω => S' k ω * (S' k ω)ᴴ) =
      expectation μ (fun ω => S k ω * (S k ω)ᴴ) := by
    intro k
    refine expectation_congr_ae ((hae k).mono fun ω hω => ?_)
    have h' : S' k ω = S k ω := hω
    show S' k ω * (S' k ω)ᴴ = S k ω * (S k ω)ᴴ
    rw [h']
  have hv2 : ∀ k, expectation μ (fun ω => (S' k ω)ᴴ * S' k ω) =
      expectation μ (fun ω => (S k ω)ᴴ * S k ω) := by
    intro k
    refine expectation_congr_ae ((hae k).mono fun ω hω => ?_)
    have h' : S' k ω = S k ω := hω
    show (S' k ω)ᴴ * S' k ω = (S k ω)ᴴ * S k ω
    rw [h']
  have hV₁' : (∑ k, expectation μ (fun ω => S' k ω * (S' k ω)ᴴ)) ≤ V₁ := by
    rw [Finset.sum_congr rfl fun k _ => hv1 k]
    exact hV₁
  have hV₂' : (∑ k, expectation μ (fun ω => (S' k ω)ᴴ * S' k ω)) ≤ V₂ := by
    rw [Finset.sum_congr rfl fun k _ => hv2 k]
    exact hV₂
  have h := intdim_bernstein_rect_tail_core (μ := μ) hmeas' hbd' hL hcent'
    hind' hV₁psd hV₂psd hV0 hV₁' hV₂' ht htv
  have hsum_ae : (fun ω => ∑ k, S' k ω) =ᵐ[μ] fun ω => ∑ k, S k ω := by
    have hall : ∀ᵐ ω ∂μ, ∀ k, S' k ω = S k ω :=
      (MeasureTheory.ae_all_iff).mpr hae
    refine hall.mono fun ω h => ?_
    show (∑ k, S' k ω) = ∑ k, S k ω
    exact Finset.sum_congr rfl fun k _ => h k
  have hmeq : μ {ω | t ≤ ‖∑ k, S' k ω‖} = μ {ω | t ≤ ‖∑ k, S k ω‖} := by
    refine MeasureTheory.measure_congr ?_
    refine hsum_ae.mono fun ω hω => ?_
    have h' : (∑ k, S' k ω) = ∑ k, S k ω := hω
    show (t ≤ ‖∑ k, S' k ω‖) = (t ≤ ‖∑ k, S k ω‖)
    rw [h']
  have hreal : μ.real {ω | t ≤ ‖∑ k, S' k ω‖} =
      μ.real {ω | t ≤ ‖∑ k, S k ω‖} := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, hmeq]
  rw [hreal] at h
  exact h

end RectTheorem

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Intrinsic Bernstein expectation bound: Corollary 7.3.2 (Tropp §7.3, §7.7.3)

**Book Corollary 7.3.2 (Intrinsic Matrix Bernstein: Expectation Bound)**:
under the hypotheses of Theorem 7.3.1,

`𝔼‖Z‖ ≤ Const·(√(v·log(1+d)) + L·log(1+d))`.

§7.7.3 proof: the layer-cake representation
`𝔼‖Z‖ = ∫₀^∞ P(‖Z‖ ≥ t) dt` (Mathlib's
`Integrable.integral_eq_integral_meas_le`), split at
`μ* = 2√(v log(1+d)) + (4/3)L log(1+d)`, the probability bounded by one
below `μ*` and by the intrinsic Bernstein tail above it, the sub-Gaussian /
sub-exponential split of the tail (`tail_exp_split`), the insert-a-factor
Gaussian integral (`integral_gaussian_tail_le`), and the exponential
integral (`integral_exp_neg_mul_Ioi`).

**Author note.** The book's split display
`exp(−t²/2/(v+Lt/3)) ≤ max{e^{−t²/(2v)}, e^{−3t/(2L)}}` is falsifiable
(at `v = 1, L = 3, t = 10` the left side is `e^{−50/11} ≈ 0.011` while the
right side is `e^{−5} ≈ 0.007`); the valid split obtained from
`v + Lt/3 ≤ 2·max{v, Lt/3}` — carries `4v` and `4L` in the denominators.
The corollary itself is unaffected (its constant is unspecified); the Lean
proof runs the corrected computation with the adjusted split point `μ*`
above and produces the explicit form

`𝔼‖Z‖ ≤ 2√(v log(1+d)) + (4/3)L log(1+d) + 4√2·√v + (16/3)L`
(`intdim_bernstein_rect_expectation_explicit`)

and the agglomerated version with the explicit constant `Const = 10`
(`intdim_bernstein_rect_expectation`, using `d ≥ 1` and `log 2 > 0.69`).

Both are stated with a.e. norm bounds (the form consumed by Corollary
7.3.3, whose independent copies inherit the bound only a.e.); the pointwise
reading follows by `Filter.Eventually.of_forall`.

-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

section IntegralToolkit

/-- **Book §7.7.3, corrected split** (C7-53): the sub-Gaussian /
sub-exponential split of the Bernstein tail —
`exp(−t²/2/(v+Lt/3)) ≤ e^{−t²/(4v)} + e^{−3t/(4L)}` (from
`v + Lt/3 ≤ 2·max{v, Lt/3}`; the book's display carries `2v`/`2L`, which is
falsifiable — see the file docstring).

**Author note.** This theorem formalizes the corrected tail split used to prove
Corollary 7.3.2; the corollary's unspecified constant is unaffected. -/
lemma tail_exp_split {v L t : ℝ} (hv : 0 < v) (hL : 0 ≤ L) (ht : 0 ≤ t) :
    Real.exp (-(t ^ 2) / 2 / (v + L * t / 3)) ≤
      Real.exp (-(t ^ 2) / (4 * v)) + Real.exp (-(3 * t) / (4 * L)) := by
  have hLt : 0 ≤ L * t / 3 := by positivity
  have hden : 0 < v + L * t / 3 := by linarith
  rcases le_total (L * t / 3) v with hcase | hcase
  · -- `v + Lt/3 ≤ 2v`: the exponent is at most `−t²/(4v)`
    have h2 : t ^ 2 / (4 * v) ≤ t ^ 2 / 2 / (v + L * t / 3) := by
      rw [div_div]
      exact div_le_div_of_nonneg_left (by positivity) (by linarith)
        (by linarith)
    have h5 : Real.exp (-(t ^ 2) / 2 / (v + L * t / 3)) ≤
        Real.exp (-(t ^ 2) / (4 * v)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_div]
      linarith
    linarith [Real.exp_pos (-(3 * t) / (4 * L))]
  · -- `v ≤ Lt/3`: the exponent is at most `−3t/(4L)` (here `L, t > 0`)
    have hLpos : 0 < L := by
      rcases eq_or_lt_of_le hL with h | h
      · exfalso
        rw [← h] at hcase
        simp only [zero_mul, zero_div] at hcase
        linarith
      · exact h
    have htpos : 0 < t := by
      rcases eq_or_lt_of_le ht with h | h
      · exfalso
        rw [← h] at hcase
        simp only [mul_zero, zero_div] at hcase
        linarith
      · exact h
    have h2 : 3 * t / (4 * L) ≤ t ^ 2 / 2 / (v + L * t / 3) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hcase, htpos, hLpos]
    have h5 : Real.exp (-(t ^ 2) / 2 / (v + L * t / 3)) ≤
        Real.exp (-(3 * t) / (4 * L)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_div]
      linarith
    linarith [Real.exp_pos (-(t ^ 2) / (4 * v))]

/-- **Book §7.7.3, Gaussian tail** (C7-53): "We controlled the Gaussian
integral by inserting the factor `√c·(t/c) ≥ 1` into the integrand":
`∫_a^∞ e^{−t²/(2c)} dt ≤ √c·e^{−a²/(2c)}` for `a ≥ √c`.  Explicit source
display (fundamental theorem of calculus on `(a, ∞)` with the antiderivative
`−√c·e^{−t²/(2c)}`). -/
lemma integral_gaussian_tail_le {c a : ℝ} (hc : 0 < c)
    (ha : Real.sqrt c ≤ a) :
    ∫ t in Set.Ioi a, Real.exp (-(t ^ 2) / (2 * c)) ≤
      Real.sqrt c * Real.exp (-(a ^ 2) / (2 * c)) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hcc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hderiv : ∀ t ∈ Set.Ioi a, HasDerivAt
      (fun s : ℝ => -(Real.sqrt c * Real.exp (-(s ^ 2) / (2 * c))))
      (t / Real.sqrt c * Real.exp (-(t ^ 2) / (2 * c))) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 : HasDerivAt (fun s : ℝ => -(s ^ 2) / (2 * c))
        (-(2 * t) / (2 * c)) t := h1.neg.div_const _
    have h3 := (h2.exp.const_mul (Real.sqrt c)).neg
    have heq : -(Real.sqrt c * (Real.exp (-(t ^ 2) / (2 * c)) *
        (-(2 * t) / (2 * c)))) =
        t / Real.sqrt c * Real.exp (-(t ^ 2) / (2 * c)) := by
      have hcc2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
      field_simp
      linear_combination t * hcc2
    rw [← heq]
    exact h3
  have hcont : ContinuousWithinAt
      (fun s : ℝ => -(Real.sqrt c * Real.exp (-(s ^ 2) / (2 * c))))
      (Set.Ici a) a := by
    apply Continuous.continuousWithinAt
    exact (continuous_const.mul (Real.continuous_exp.comp
      ((continuous_pow 2).neg.div_const _))).neg
  have hlim : Filter.Tendsto
      (fun s : ℝ => -(Real.sqrt c * Real.exp (-(s ^ 2) / (2 * c))))
      Filter.atTop (nhds 0) := by
    have h4 : Filter.Tendsto (fun s : ℝ => -(s ^ 2) / (2 * c))
        Filter.atTop Filter.atBot := by
      refine Filter.Tendsto.atBot_div_const (by positivity) ?_
      exact Filter.tendsto_neg_atTop_atBot.comp
        (Filter.tendsto_pow_atTop two_ne_zero)
    have h5 := Real.tendsto_exp_atBot.comp h4
    have h6 := (h5.const_mul (Real.sqrt c)).neg
    simpa using h6
  have hF'int : IntegrableOn
      (fun t : ℝ => t / Real.sqrt c * Real.exp (-(t ^ 2) / (2 * c)))
      (Set.Ioi a) := by
    have h6 : Integrable (fun t : ℝ =>
        t * Real.exp (-(1 / (2 * c)) * t ^ 2)) volume :=
      integrable_mul_exp_neg_mul_sq (by positivity)
    have h7 : (fun t : ℝ => t / Real.sqrt c *
        Real.exp (-(t ^ 2) / (2 * c))) =
        fun t : ℝ => (1 / Real.sqrt c) *
          (t * Real.exp (-(1 / (2 * c)) * t ^ 2)) := by
      funext t
      have h8 : -(1 / (2 * c)) * t ^ 2 = -(t ^ 2) / (2 * c) := by ring
      rw [h8]
      ring
    rw [h7]
    exact (h6.const_mul _).integrableOn
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont
    hderiv hF'int hlim
  have hcomp : ∀ t ∈ Set.Ioi a, Real.exp (-(t ^ 2) / (2 * c)) ≤
      t / Real.sqrt c * Real.exp (-(t ^ 2) / (2 * c)) := by
    intro t htt
    have h8 : 1 ≤ t / Real.sqrt c := by
      rw [le_div_iff₀ hsc, one_mul]
      exact ha.trans (le_of_lt htt)
    calc Real.exp (-(t ^ 2) / (2 * c)) =
        1 * Real.exp (-(t ^ 2) / (2 * c)) := (one_mul _).symm
      _ ≤ t / Real.sqrt c * Real.exp (-(t ^ 2) / (2 * c)) :=
        mul_le_mul_of_nonneg_right h8 (Real.exp_pos _).le
  have hint1 : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2) / (2 * c)))
      (Set.Ioi a) := by
    have h9 : Integrable (fun t : ℝ =>
        Real.exp (-(1 / (2 * c)) * t ^ 2)) volume :=
      integrable_exp_neg_mul_sq (by positivity)
    have h10 : (fun t : ℝ => Real.exp (-(t ^ 2) / (2 * c))) =
        fun t : ℝ => Real.exp (-(1 / (2 * c)) * t ^ 2) := by
      funext t
      congr 1
      ring
    rw [h10]
    exact h9.integrableOn
  calc ∫ t in Set.Ioi a, Real.exp (-(t ^ 2) / (2 * c))
      ≤ ∫ t in Set.Ioi a,
          t / Real.sqrt c * Real.exp (-(t ^ 2) / (2 * c)) :=
        setIntegral_mono_on hint1 hF'int measurableSet_Ioi hcomp
    _ = 0 - -(Real.sqrt c * Real.exp (-(a ^ 2) / (2 * c))) := hFTC
    _ = Real.sqrt c * Real.exp (-(a ^ 2) / (2 * c)) := by ring

/-- **Book §7.7.3, exponential tail** (C7-53): `∫_a^∞ e^{−bt} dt = e^{−ba}/b`
for `b > 0`.  Implicit source display (fundamental theorem of calculus on
`(a, ∞)`). -/
lemma integral_exp_neg_mul_Ioi {b a : ℝ} (hb : 0 < b) :
    ∫ t in Set.Ioi a, Real.exp (-(b * t)) = Real.exp (-(b * a)) / b := by
  have hderiv : ∀ t ∈ Set.Ioi a, HasDerivAt
      (fun s : ℝ => -(Real.exp (-(b * s)) / b)) (Real.exp (-(b * t))) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => -(b * s)) (-b) t := by
      have h0 : HasDerivAt (fun s : ℝ => b * s) b t := by
        simpa using (hasDerivAt_id t).const_mul b
      exact h0.neg
    have h2 := (h1.exp.div_const b).neg
    have heq : -(Real.exp (-(b * t)) * -b / b) = Real.exp (-(b * t)) := by
      field_simp
    rw [← heq]
    exact h2
  have hcont : ContinuousWithinAt
      (fun s : ℝ => -(Real.exp (-(b * s)) / b)) (Set.Ici a) a := by
    apply Continuous.continuousWithinAt
    exact ((Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).neg)).div_const b).neg
  have hlim : Filter.Tendsto (fun s : ℝ => -(Real.exp (-(b * s)) / b))
      Filter.atTop (nhds 0) := by
    have h4 : Filter.Tendsto (fun s : ℝ => -(b * s))
        Filter.atTop Filter.atBot := by
      exact Filter.tendsto_neg_atTop_atBot.comp
        (Filter.Tendsto.const_mul_atTop hb Filter.tendsto_id)
    have h5 := Real.tendsto_exp_atBot.comp h4
    have h6 := (h5.div_const b).neg
    simpa using h6
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(b * t)))
      (Set.Ioi a) := by
    have h7 := exp_neg_integrableOn_Ioi a hb
    simpa [neg_mul] using h7
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont
    hderiv hint hlim
  rw [hFTC]
  ring

end IntegralToolkit

section MainCorollary

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {S : ι → Ω → Matrix m n ℂ} {L : ℝ}
variable {V₁ : Matrix m m ℂ} {V₂ : Matrix n n ℂ}
variable [Nonempty (m ⊕ n)]

/-- Lean implementation helper: the explicit coefficient calculation underlying
**Book Corollary 7.3.2**, using the corrected split and the split point
`μ* = 2√(v log(1+d)) + (4/3)L log(1+d)`:

`𝔼‖Z‖ ≤ 2√(v log(1+d)) + (4/3)L log(1+d) + 4√2·√v + (16/3)L`.

**Author note.** The book leaves `Const` unspecified; this helper exposes every
coefficient before the final agglomeration. -/
theorem intdim_bernstein_rect_expectation_explicit
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ L)
    (hL : 0 ≤ L) (hcent : ∀ k, expectation μ (S k) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ)
    (hV₁psd : V₁.PosSemidef) (hV₂psd : V₂.PosSemidef)
    (hV0 : ¬(V₁ = 0 ∧ V₂ = 0))
    (hV₁ : (∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)) ≤ V₁)
    (hV₂ : (∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)) ≤ V₂) :
    ∫ ω, ‖∑ k, S k ω‖ ∂μ ≤
      2 * Real.sqrt (max ‖V₁‖ ‖V₂‖ *
          Real.log (1 + intdim (Matrix.fromBlocks V₁ 0 0 V₂))) +
        4 / 3 * L * Real.log (1 + intdim (Matrix.fromBlocks V₁ 0 0 V₂)) +
        4 * Real.sqrt 2 * Real.sqrt (max ‖V₁‖ ‖V₂‖) + 16 / 3 * L := by
  classical
  set v : ℝ := max ‖V₁‖ ‖V₂‖ with hvdef
  set d : ℝ := intdim (Matrix.fromBlocks V₁ 0 0 V₂) with hddef
  have hvpos : 0 < v := by
    rcases (not_and_or.mp hV0) with h | h
    · exact lt_max_of_lt_left (norm_pos_iff.mpr h)
    · exact lt_max_of_lt_right (norm_pos_iff.mpr h)
  have hd1 : 1 ≤ d := one_le_intdim
    (posSemidef_fromBlocks_diag hV₁psd hV₂psd)
    (fun h => hV0 (fromBlocks_diag_eq_zero_iff.mp h))
  have hd0 : 0 ≤ d := zero_le_one.trans hd1
  set lg : ℝ := Real.log (1 + d) with hlgdef
  have hlg2 : Real.log 2 ≤ lg := Real.log_le_log two_pos (by linarith)
  have hlg69 : (0.69 : ℝ) ≤ lg :=
    le_trans (by linarith [Real.log_two_gt_d9]) hlg2
  have hlgpos : 0 < lg := lt_of_lt_of_le (by norm_num) hlg69
  set μstar : ℝ := 2 * Real.sqrt (v * lg) + 4 / 3 * L * lg with hμdef
  have hμnn : 0 ≤ μstar := by
    have h1 : 0 ≤ Real.sqrt (v * lg) := Real.sqrt_nonneg _
    have h2 : 0 ≤ 4 / 3 * L * lg := by positivity
    simp only [hμdef]
    linarith
  -- integrability of `‖Z‖`
  have hballae : ∀ᵐ ω ∂μ, ∀ k, ‖S k ω‖ ≤ L := (MeasureTheory.ae_all_iff).mpr hbd
  have hsummeas : Measurable fun ω => ∑ k, S k ω := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    have h0 : (fun ω => (∑ k, S k ω) i j) = fun ω => ∑ k, S k ω i j := by
      funext ω
      rw [Matrix.sum_apply]
    show Measurable fun ω => (∑ k, S k ω) i j
    rw [h0]
    exact Finset.measurable_sum _ fun k _ =>
      (measurable_entry i j).comp (hmeas k)
  have hZmeas : Measurable fun ω => ‖∑ k, S k ω‖ :=
    continuous_l2_opNorm.measurable.comp hsummeas
  have hZint : Integrable (fun ω => ‖∑ k, S k ω‖) μ := by
    refine Integrable.of_bound hZmeas.aestronglyMeasurable
      ((Fintype.card ι : ℝ) * L) ?_
    refine hballae.mono fun ω h => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc ‖∑ k, S k ω‖ ≤ ∑ k, ‖S k ω‖ := norm_sum_le _ _
      _ ≤ ∑ _k : ι, L := Finset.sum_le_sum fun k _ => h k
      _ = (Fintype.card ι : ℝ) * L := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the degenerate case `L = 0`: all summands vanish a.e.
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · have hZ0 : (fun ω => ‖∑ k, S k ω‖) =ᵐ[μ] fun _ => (0 : ℝ) := by
      refine hballae.mono fun ω h => ?_
      have h1 : ∀ k, S k ω = 0 := fun k => by
        have h2 := h k
        rw [← hL0] at h2
        exact norm_le_zero_iff.mp h2
      show ‖∑ k, S k ω‖ = 0
      rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_const_zero,
        norm_zero]
    have hzero : ∫ ω, ‖∑ k, S k ω‖ ∂μ = 0 := by
      rw [integral_congr_ae hZ0, integral_zero]
    rw [hzero]
    have h1 : 0 ≤ Real.sqrt (v * lg) := Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
    have h3 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have h4 : 0 ≤ L * lg := mul_nonneg hL hlgpos.le
    nlinarith [mul_nonneg h3 h2]
  -- the main case `0 < L`: layer cake
  have hlc := hZint.integral_eq_integral_meas_le
    (Filter.Eventually.of_forall fun ω => norm_nonneg _)
  set g : ℝ → ℝ := fun t => μ.real {ω | t ≤ ‖∑ k, S k ω‖} with hgdef
  have hganti : Antitone g := fun t₁ t₂ h12 =>
    measureReal_mono fun ω hω => le_trans h12 hω
  have hgmeas : Measurable g := hganti.measurable
  have hg1 : ∀ t, g t ≤ 1 := fun t => by
    have h := measureReal_mono (μ := μ)
      (Set.subset_univ {ω | t ≤ ‖∑ k, S k ω‖})
    rwa [probReal_univ] at h
  have hgnn : ∀ t, 0 ≤ g t := fun t => measureReal_nonneg
  -- the split point exceeds the Bernstein threshold
  have hsqrt4 : Real.sqrt (4 * (v * lg)) = 2 * Real.sqrt (v * lg) := by
    rw [show (4 : ℝ) * (v * lg) = 2 ^ 2 * (v * lg) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hμthresh : Real.sqrt v + L / 3 ≤ μstar := by
    have h1 : Real.sqrt v ≤ 2 * Real.sqrt (v * lg) := by
      rw [← hsqrt4]
      apply Real.sqrt_le_sqrt
      nlinarith [hlg69, hvpos]
    have h2 : L / 3 ≤ 4 / 3 * L * lg := by nlinarith [hlg69, hL]
    simp only [hμdef]
    linarith
  -- tail bound above the split point
  have htail : ∀ t ∈ Set.Ioi μstar, g t ≤
      4 * d * (Real.exp (-(t ^ 2) / (4 * v)) +
        Real.exp (-(3 * t) / (4 * L))) := by
    intro t htt
    have h1 : Real.sqrt v + L / 3 ≤ t := hμthresh.trans (le_of_lt htt)
    have h2 := intdim_bernstein_rect_tail_ae (μ := μ) hmeas hbd hL hcent
      hind hV₁psd hV₂psd hV0 hV₁ hV₂ h1
    have htnn : 0 ≤ t := hμnn.trans (le_of_lt htt)
    have h3 := tail_exp_split hvpos hL htnn
    calc g t ≤ 4 * d * Real.exp (-(t ^ 2) / 2 / (v + L * t / 3)) := h2
      _ ≤ 4 * d * (Real.exp (-(t ^ 2) / (4 * v)) +
          Real.exp (-(3 * t) / (4 * L))) := by
          apply mul_le_mul_of_nonneg_left h3
          nlinarith [hd1]
  -- integrability of the pieces
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 μstar) := by
    refine integrableOn_const ?_
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hint1 : IntegrableOn g (Set.Ioc 0 μstar) := by
    refine Integrable.mono' hconst hgmeas.aestronglyMeasurable.restrict ?_
    refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hgnn t)]
    exact hg1 t
  have hint_g1 : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2) / (4 * v)))
      (Set.Ioi μstar) := by
    have h9 : Integrable (fun t : ℝ =>
        Real.exp (-(1 / (4 * v)) * t ^ 2)) volume :=
      integrable_exp_neg_mul_sq (by positivity)
    have h10 : (fun t : ℝ => Real.exp (-(t ^ 2) / (4 * v))) =
        fun t : ℝ => Real.exp (-(1 / (4 * v)) * t ^ 2) := by
      funext t
      congr 1
      ring
    rw [h10]
    exact h9.integrableOn
  have hint_g2 : IntegrableOn (fun t : ℝ => Real.exp (-(3 * t) / (4 * L)))
      (Set.Ioi μstar) := by
    have h9 := exp_neg_integrableOn_Ioi μstar
      (b := 3 / (4 * L)) (by positivity)
    have h10 : (fun t : ℝ => Real.exp (-(3 * t) / (4 * L))) =
        fun t : ℝ => Real.exp (-(3 / (4 * L)) * t) := by
      funext t
      congr 1
      ring
    rw [h10]
    simpa [neg_mul] using h9
  have hmajint : IntegrableOn (fun t : ℝ => 4 * d *
      (Real.exp (-(t ^ 2) / (4 * v)) + Real.exp (-(3 * t) / (4 * L))))
      (Set.Ioi μstar) := (hint_g1.add hint_g2).const_mul _
  have hint2 : IntegrableOn g (Set.Ioi μstar) := by
    refine Integrable.mono' hmajint hgmeas.aestronglyMeasurable.restrict ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t htt => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hgnn t)]
    exact htail t htt
  -- split the layer-cake integral at `μ*`
  have hsplit : ∫ t in Set.Ioi (0 : ℝ), g t =
      (∫ t in Set.Ioc 0 μstar, g t) + ∫ t in Set.Ioi μstar, g t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hμnn]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hint1 hint2
  have hpart1 : ∫ t in Set.Ioc (0 : ℝ) μstar, g t ≤ μstar := by
    calc ∫ t in Set.Ioc (0 : ℝ) μstar, g t
        ≤ ∫ _t in Set.Ioc (0 : ℝ) μstar, (1 : ℝ) :=
          setIntegral_mono_on hint1 hconst measurableSet_Ioc
            fun t _ => hg1 t
      _ = μstar := by
          rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
            Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
          ring
  -- the two tail integrals
  have hgauss : ∫ t in Set.Ioi μstar, Real.exp (-(t ^ 2) / (4 * v)) ≤
      Real.sqrt (2 * v) * (1 + d)⁻¹ := by
    have hshape : (fun t : ℝ => Real.exp (-(t ^ 2) / (4 * v))) =
        fun t : ℝ => Real.exp (-(t ^ 2) / (2 * (2 * v))) := by
      funext t
      congr 1
      ring
    have hsqrt2v : Real.sqrt (2 * v) ≤ μstar := by
      have h1 : Real.sqrt (2 * v) ≤ 2 * Real.sqrt (v * lg) := by
        rw [← hsqrt4]
        apply Real.sqrt_le_sqrt
        nlinarith [hlg69, hvpos]
      have h2 : 0 ≤ 4 / 3 * L * lg := by positivity
      simp only [hμdef]
      linarith
    have h1 := integral_gaussian_tail_le (c := 2 * v) (by positivity)
      hsqrt2v
    rw [hshape]
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    -- `e^{−μ*²/(4v)} ≤ (1+d)⁻¹` since `μ*² ≥ 4v·log(1+d)`
    have h2 : 4 * (v * lg) ≤ μstar ^ 2 := by
      have h3 : 2 * Real.sqrt (v * lg) ≤ μstar := by
        have h4 : 0 ≤ 4 / 3 * L * lg := by positivity
        simp only [hμdef]
        linarith
      have h5 : (2 * Real.sqrt (v * lg)) ^ 2 = 4 * (v * lg) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring
      nlinarith [Real.sqrt_nonneg (v * lg), h3, h5]
    have h6 : -(μstar ^ 2) / (2 * (2 * v)) ≤ -lg := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [h2]
    calc Real.exp (-(μstar ^ 2) / (2 * (2 * v))) ≤ Real.exp (-lg) :=
        Real.exp_le_exp.mpr h6
      _ = (1 + d)⁻¹ := by
          rw [Real.exp_neg, hlgdef, Real.exp_log (by linarith)]
  have hexp : ∫ t in Set.Ioi μstar, Real.exp (-(3 * t) / (4 * L)) ≤
      4 * L / 3 * (1 + d)⁻¹ := by
    have hshape : (fun t : ℝ => Real.exp (-(3 * t) / (4 * L))) =
        fun t : ℝ => Real.exp (-(3 / (4 * L) * t)) := by
      funext t
      congr 1
      ring
    have h1 := integral_exp_neg_mul_Ioi (b := 3 / (4 * L)) (a := μstar)
      (by positivity)
    rw [hshape, h1]
    have h2 : lg ≤ 3 / (4 * L) * μstar := by
      rw [hμdef, mul_add]
      have h4 : 3 / (4 * L) * (4 / 3 * L * lg) = lg := by
        field_simp
      rw [h4]
      have h5 : 0 ≤ 3 / (4 * L) * (2 * Real.sqrt (v * lg)) :=
        mul_nonneg (div_nonneg (by norm_num) (by linarith))
          (by positivity)
      linarith
    have h5 : Real.exp (-(3 / (4 * L) * μstar)) ≤ (1 + d)⁻¹ := by
      calc Real.exp (-(3 / (4 * L) * μstar)) ≤ Real.exp (-lg) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = (1 + d)⁻¹ := by
            rw [Real.exp_neg, hlgdef, Real.exp_log (by linarith)]
    calc Real.exp (-(3 / (4 * L) * μstar)) / (3 / (4 * L))
        = Real.exp (-(3 / (4 * L) * μstar)) * (4 * L / 3) := by
          rw [div_eq_mul_inv, inv_div]
      _ ≤ (1 + d)⁻¹ * (4 * L / 3) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = 4 * L / 3 * (1 + d)⁻¹ := by ring
  have hpart2 : ∫ t in Set.Ioi μstar, g t ≤
      4 * Real.sqrt (2 * v) + 16 / 3 * L := by
    have hd1' : d * (1 + d)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ (by linarith), one_mul]
      linarith
    calc ∫ t in Set.Ioi μstar, g t
        ≤ ∫ t in Set.Ioi μstar, 4 * d *
            (Real.exp (-(t ^ 2) / (4 * v)) +
              Real.exp (-(3 * t) / (4 * L))) :=
          setIntegral_mono_on hint2 hmajint measurableSet_Ioi htail
      _ = 4 * d * ((∫ t in Set.Ioi μstar, Real.exp (-(t ^ 2) / (4 * v))) +
            ∫ t in Set.Ioi μstar, Real.exp (-(3 * t) / (4 * L))) := by
          rw [integral_const_mul, integral_add hint_g1 hint_g2]
      _ ≤ 4 * d * (Real.sqrt (2 * v) * (1 + d)⁻¹ +
            4 * L / 3 * (1 + d)⁻¹) := by
          apply mul_le_mul_of_nonneg_left (add_le_add hgauss hexp)
          nlinarith [hd1]
      _ = 4 * (d * (1 + d)⁻¹) * (Real.sqrt (2 * v) + 4 * L / 3) := by
          ring
      _ ≤ 4 * 1 * (Real.sqrt (2 * v) + 4 * L / 3) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left hd1' (by norm_num)
          · have := Real.sqrt_nonneg (2 * v)
            nlinarith [hLpos]
      _ = 4 * Real.sqrt (2 * v) + 16 / 3 * L := by ring
  -- assemble
  have hsqrt2v_eq : Real.sqrt (2 * v) = Real.sqrt 2 * Real.sqrt v :=
    Real.sqrt_mul (by norm_num) v
  calc ∫ ω, ‖∑ k, S k ω‖ ∂μ = ∫ t in Set.Ioi (0 : ℝ), g t := hlc
    _ = (∫ t in Set.Ioc 0 μstar, g t) + ∫ t in Set.Ioi μstar, g t := hsplit
    _ ≤ μstar + (4 * Real.sqrt (2 * v) + 16 / 3 * L) :=
        add_le_add hpart1 hpart2
    _ = 2 * Real.sqrt (v * lg) + 4 / 3 * L * lg +
        4 * Real.sqrt 2 * Real.sqrt v + 16 / 3 * L := by
        rw [hμdef, hsqrt2v_eq]
        ring

/-- **Book Corollary 7.3.2 (Intrinsic Matrix Bernstein: Expectation Bound)**:

`𝔼‖Z‖ ≤ Const·(√(v·log(1+d)) + L·log(1+d))`

with the unspecified `Const` instantiated at the explicit value `10`
(documented constant chase from the explicit form, using `d ≥ 1` and
`log 2 > 0.69`).  Explicit source declaration; §7.7.3 proof.

**Author note.** Lean supplies the concrete admissible value `Const = 10` and
states the a.e. norm bounds needed by the sampling application explicitly. -/
theorem intdim_bernstein_rect_expectation
    (hmeas : ∀ k, Measurable (S k)) (hbd : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ L)
    (hL : 0 ≤ L) (hcent : ∀ k, expectation μ (S k) = 0)
    (hind : ProbabilityTheory.iIndepFun S μ)
    (hV₁psd : V₁.PosSemidef) (hV₂psd : V₂.PosSemidef)
    (hV0 : ¬(V₁ = 0 ∧ V₂ = 0))
    (hV₁ : (∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)) ≤ V₁)
    (hV₂ : (∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)) ≤ V₂) :
    ∫ ω, ‖∑ k, S k ω‖ ∂μ ≤
      10 * (Real.sqrt (max ‖V₁‖ ‖V₂‖ *
          Real.log (1 + intdim (Matrix.fromBlocks V₁ 0 0 V₂))) +
        L * Real.log (1 + intdim (Matrix.fromBlocks V₁ 0 0 V₂))) := by
  refine (intdim_bernstein_rect_expectation_explicit hmeas hbd hL hcent
    hind hV₁psd hV₂psd hV0 hV₁ hV₂).trans ?_
  set v : ℝ := max ‖V₁‖ ‖V₂‖ with hvdef
  set d : ℝ := intdim (Matrix.fromBlocks V₁ 0 0 V₂) with hddef
  have hvpos : 0 < v := by
    rcases (not_and_or.mp hV0) with h | h
    · exact lt_max_of_lt_left (norm_pos_iff.mpr h)
    · exact lt_max_of_lt_right (norm_pos_iff.mpr h)
  have hd1 : 1 ≤ d := one_le_intdim
    (posSemidef_fromBlocks_diag hV₁psd hV₂psd)
    (fun h => hV0 (fromBlocks_diag_eq_zero_iff.mp h))
  set lg : ℝ := Real.log (1 + d) with hlgdef
  have hlg69 : (0.69 : ℝ) ≤ lg := by
    have h1 : Real.log 2 ≤ lg := Real.log_le_log two_pos (by linarith)
    linarith [Real.log_two_gt_d9]
  have hlgpos : 0 < lg := lt_of_lt_of_le (by norm_num) hlg69
  have hmul : Real.sqrt (v * lg) = Real.sqrt v * Real.sqrt lg :=
    Real.sqrt_mul hvpos.le lg
  have hslg : (0.83 : ℝ) ≤ Real.sqrt lg := by
    rw [show (0.83 : ℝ) = Real.sqrt (0.83 ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [hlg69]
  have h5 : Real.sqrt v * 0.83 ≤ Real.sqrt (v * lg) := by
    rw [hmul]
    exact mul_le_mul_of_nonneg_left hslg (Real.sqrt_nonneg v)
  have h3 : Real.sqrt 2 ≤ 1.415 := by
    rw [show (1.415 : ℝ) = Real.sqrt (1.415 ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    norm_num
  have hA : 4 * Real.sqrt 2 * Real.sqrt v ≤ 8 * Real.sqrt (v * lg) := by
    have h6 : Real.sqrt 2 * Real.sqrt v ≤ 1.415 * Real.sqrt v :=
      mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg v)
    nlinarith [h5, h6, Real.sqrt_nonneg v]
  have hB : 16 / 3 * L ≤ 8 * (L * lg) := by
    have h7 : L * 0.69 ≤ L * lg := mul_le_mul_of_nonneg_left hlg69 hL
    nlinarith [h7]
  linarith [hA, hB]

end MainCorollary

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Sampling estimators and randomized multiplication (Tropp §7.3.2–§7.3.3)

**Book Corollary 7.3.3 (Matrix Approximation by Random Sampling: Intrinsic
Dimension Bounds)**: for the Chapter-6
sampling model (`𝔼R = B`, `‖R‖ ≤ L`, psd upper bounds `M₁ ≽ 𝔼(RR*)`,
`M₂ ≽ 𝔼(R*R)`, `d = intdim(diag(M₁,M₂))`, `m = max{‖M₁‖,‖M₂‖}`, and
`R̄_n = n⁻¹ΣR_k` over independent copies):

* tail:
  `P(‖R̄_n − B‖ ≥ t) ≤ 4d·exp(−nt²/2/(m + 2Lt/3))` for `t ≥ √m + L/3`
  (`matrix_sampling_intdim_tail`);
* expectation, with the unspecified `Const`
  made explicit:
  `𝔼‖R̄_n − B‖ ≤ 10·√(m log(1+d)/n) + 20·L log(1+d)/n`
  (`matrix_sampling_intdim_expectation`).

The book omits the proof ("similar with that of Corollary 6.2.1"); the Lean
proof mirrors the Chapter-6 reductions (`S_k = n⁻¹(R_k − B)`, a.e. bound
`‖S_k‖ ≤ 2L/n`, the Loewner variance transfer `Σ𝔼S_kS_k* ≼ n⁻¹M₁` via
`matrixVar₁ ≼ 𝔼RR*` and law transfer) and applies Theorem 7.3.1 /
Corollary 7.3.2.  **Author note.** For `n = 1` the stated
threshold `t ≥ √m + L/3` does not imply the nonvacuousness condition
`nt² ≥ m + 2Lt/3` of the §7.7.1 argument; in the gap the right-hand side
exceeds `4d·e^{−1/2} ≥ 2 > 1 ≥ P` (using `d ≥ 1`), so the statement is
still true — the Lean proof runs this case analysis.

**§7.3.3 (Application: Randomized Matrix Multiplication)**: for the
Chapter-6 randomized multiplication model under `‖B‖ = ‖C‖ = 1` and
`asr = (srank B + srank C)/2`:

* the §6.4 facts recalled by the source — `‖R‖ ≤ asr` (Chapter 6's
  `matmul_norm_le`) and the Loewner bounds `𝔼(RR*) ≼ 2·asr·BB*`,
  `𝔼(R*R) ≼ 2·asr·C*C` (`matmul_var1_le`, `matmul_var2_le`, extracted here
  from the §6.4.3 computation);
* `d ≤ intdim(M₁) + intdim(M₂) = srank(B) + srank(C) = 2·asr` and
  `m = 2·asr` (C7-25/C7-26, via file 01);
* the final display (C7-27), with explicit constants
  (`log(1+2asr) ≤ 2log(1+asr)` absorbs the remaining factors):
  `𝔼‖R̄_n − BC‖ ≤ 20·√(asr·log(1+asr)/n) + 40·asr·log(1+asr)/n`
  (`matmul_intdim_error_bound`);
* the sample-count consequence (C7-28): `n ≥ ε⁻²·asr·log(1+asr)` gives
  `𝔼‖R̄_n − BC‖ ≤ 20ε + 40ε²` (`matmul_intdim_sample_cost`).

-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [IsProbabilityMeasure μ]
variable {R₀ : Ω → Matrix m n ℂ} {B : Matrix m n ℂ} {L : ℝ} {nn : ℕ}
variable {R : Fin nn → Ω → Matrix m n ℂ}
variable {M₁ : Matrix m m ℂ} {M₂ : Matrix n n ℂ}

section SamplingEstimator

variable [Nonempty (m ⊕ n)]

/-- Lean implementation helper (the Loewner half of the Chapter-6 variance
reduction): `Σ_k 𝔼(S_kS_k*) ≼ n⁻¹·M₁` for `S_k = n⁻¹(R_k − B)`, from
`matrixVar₁(R₀) ≼ 𝔼(R₀R₀*) ≼ M₁` and the law transfer to the copies. -/
lemma sampling_S_var1 (hnn : 0 < nn)
    (hR₀m : Measurable R₀) (hbd : ∀ ω, ‖R₀ ω‖ ≤ L)
    (hmean : expectation μ R₀ = B)
    (hM₁ : expectation μ (fun ω => R₀ ω * (R₀ ω)ᴴ) ≤ M₁)
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀ μ μ) :
    (∑ k, expectation μ (fun ω =>
        ((nn : ℝ)⁻¹ • (R k ω - B)) * ((nn : ℝ)⁻¹ • (R k ω - B))ᴴ)) ≤
      (nn : ℝ)⁻¹ • M₁ := by
  classical
  set c : ℝ := (nn : ℝ)⁻¹ with hcdef
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  have hc0 : 0 ≤ c := by positivity
  have hSid : ∀ k, ProbabilityTheory.IdentDistrib
      (fun ω => c • (R k ω - B)) (fun ω => c • (R₀ ω - B)) μ μ := fun k => by
    have hg : Measurable fun M : Matrix m n ℂ => c • (M - B) := by
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      show Measurable fun M : Matrix m n ℂ => c • (M i j - B i j)
      exact Measurable.const_smul ((measurable_entry i j).sub_const (B i j)) c
    exact (hid k).comp hg
  have hR₀1 : MIntegrable (fun ω => R₀ ω * (R₀ ω)ᴴ) μ :=
    MIntegrable.of_bound (measurable_matrix_mul_conjTranspose hR₀m) (L * L)
      (Filter.Eventually.of_forall fun ω i j => by
        calc ‖(R₀ ω * (R₀ ω)ᴴ) i j‖ ≤ ‖R₀ ω * (R₀ ω)ᴴ‖ :=
              norm_entry_le_l2_opNorm_rect _ _ _
        _ ≤ ‖R₀ ω‖ * ‖(R₀ ω)ᴴ‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖R₀ ω‖ * ‖R₀ ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ L * L := by nlinarith [norm_nonneg (R₀ ω), hbd ω])
  have hSS : ∀ k, expectation μ (fun ω =>
      (c • (R k ω - B)) * (c • (R k ω - B))ᴴ) =
      (c * c) • matrixVar1 μ R₀ := by
    intro k
    have h1 := expectation_mul_conjTranspose_of_identDistrib (hSid k)
    rw [h1]
    have h2 : (fun ω => (c • (R₀ ω - B)) * (c • (R₀ ω - B))ᴴ) =
        fun ω => (c * c) • ((R₀ ω - B) * (R₀ ω - B)ᴴ) := by
      funext ω
      rw [conjTranspose_real_smul_rect, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul]
    rw [h2, expectation_real_smul]
    congr 1
    rw [matrixVar1, hmean]
  have hvar : matrixVar1 μ R₀ ≤ M₁ :=
    (centered_second_moment_le (mintegrable_rect_of_norm_bound hR₀m hbd)
      hR₀1).trans hM₁
  calc (∑ k, expectation μ (fun ω =>
      (c • (R k ω - B)) * (c • (R k ω - B))ᴴ))
      ≤ ∑ _k : Fin nn, (c * c) • M₁ := by
        refine sum_loewner_mono Finset.univ fun k _ => ?_
        rw [hSS k]
        exact real_smul_loewner_mono (by positivity) hvar
    _ = c • M₁ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        congr 1
        rw [hcdef]
        field_simp
    _ = (nn : ℝ)⁻¹ • M₁ := by rw [hcdef]

/-- Lean implementation helper: the `Σ𝔼(S_k*S_k) ≼ n⁻¹·M₂` mirror. -/
lemma sampling_S_var2 (hnn : 0 < nn)
    (hR₀m : Measurable R₀) (hbd : ∀ ω, ‖R₀ ω‖ ≤ L)
    (hmean : expectation μ R₀ = B)
    (hM₂ : expectation μ (fun ω => (R₀ ω)ᴴ * R₀ ω) ≤ M₂)
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀ μ μ) :
    (∑ k, expectation μ (fun ω =>
        ((nn : ℝ)⁻¹ • (R k ω - B))ᴴ * ((nn : ℝ)⁻¹ • (R k ω - B)))) ≤
      (nn : ℝ)⁻¹ • M₂ := by
  classical
  set c : ℝ := (nn : ℝ)⁻¹ with hcdef
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  have hc0 : 0 ≤ c := by positivity
  have hSid : ∀ k, ProbabilityTheory.IdentDistrib
      (fun ω => c • (R k ω - B)) (fun ω => c • (R₀ ω - B)) μ μ := fun k => by
    have hg : Measurable fun M : Matrix m n ℂ => c • (M - B) := by
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      show Measurable fun M : Matrix m n ℂ => c • (M i j - B i j)
      exact Measurable.const_smul ((measurable_entry i j).sub_const (B i j)) c
    exact (hid k).comp hg
  have hR₀2 : MIntegrable (fun ω => (R₀ ω)ᴴ * R₀ ω) μ :=
    MIntegrable.of_bound (measurable_matrix_conjTranspose_mul hR₀m) (L * L)
      (Filter.Eventually.of_forall fun ω i j => by
        calc ‖((R₀ ω)ᴴ * R₀ ω) i j‖ ≤ ‖(R₀ ω)ᴴ * R₀ ω‖ :=
              norm_entry_le_l2_opNorm_rect _ _ _
        _ ≤ ‖(R₀ ω)ᴴ‖ * ‖R₀ ω‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖R₀ ω‖ * ‖R₀ ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ L * L := by nlinarith [norm_nonneg (R₀ ω), hbd ω])
  have hSS2 : ∀ k, expectation μ (fun ω =>
      (c • (R k ω - B))ᴴ * (c • (R k ω - B))) =
      (c * c) • matrixVar2 μ R₀ := by
    intro k
    have h1 := expectation_conjTranspose_mul_of_identDistrib (hSid k)
    rw [h1]
    have h2 : (fun ω => (c • (R₀ ω - B))ᴴ * (c • (R₀ ω - B))) =
        fun ω => (c * c) • ((R₀ ω - B)ᴴ * (R₀ ω - B)) := by
      funext ω
      rw [conjTranspose_real_smul_rect, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul]
    rw [h2, expectation_real_smul]
    congr 1
    rw [matrixVar2, hmean]
  have hvar : matrixVar2 μ R₀ ≤ M₂ :=
    (centered_second_moment_le₂ (mintegrable_rect_of_norm_bound hR₀m hbd)
      hR₀2).trans hM₂
  calc (∑ k, expectation μ (fun ω =>
      (c • (R k ω - B))ᴴ * (c • (R k ω - B))))
      ≤ ∑ _k : Fin nn, (c * c) • M₂ := by
        refine sum_loewner_mono Finset.univ fun k _ => ?_
        rw [hSS2 k]
        exact real_smul_loewner_mono (by positivity) hvar
    _ = c • M₂ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        congr 1
        rw [hcdef]
        field_simp
    _ = (nn : ℝ)⁻¹ • M₂ := by rw [hcdef]

/-- Lean implementation helper: the scaled block-diagonal intrinsic
dimension of the sampling reduction agrees with `d = intdim(diag(M₁,M₂))`. -/
lemma intdim_fromBlocks_smul_inv (hnn : 0 < nn) :
    intdim (Matrix.fromBlocks ((nn : ℝ)⁻¹ • M₁) 0 0 ((nn : ℝ)⁻¹ • M₂)) =
      intdim (Matrix.fromBlocks M₁ 0 0 M₂) := by
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  have hblocks : Matrix.fromBlocks ((nn : ℝ)⁻¹ • M₁) 0 0 ((nn : ℝ)⁻¹ • M₂) =
      (nn : ℝ)⁻¹ • Matrix.fromBlocks M₁ 0 0 M₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.smul_apply]
  rw [hblocks, intdim_smul (by positivity)]

/-- **Book Corollary 7.3.3, tail bound** (C7-23):

`P(‖R̄_n − B‖ ≥ t) ≤ 4d·exp(−nt²/2/(m + 2Lt/3))` for `t ≥ √m + L/3`,

with `d = intdim(diag(M₁,M₂))`, `m = max{‖M₁‖,‖M₂‖}` for psd upper bounds
`M₁ ≽ 𝔼(RR*)`, `M₂ ≽ 𝔼(R*R)`.  The source omits the proof as similar to
Corollary 6.2.1.

**Author note.** Lean handles the `n = 1` gap in the stated threshold by a
vacuous-bound branch and explicitly assumes `¬(M₁ = 0 ∧ M₂ = 0)` to avoid
the degenerate intrinsic-dimension denominator.  See
`matrix_sampling_intdim_tail_ae` for the source-faithful almost-sure template
counterpart. -/
theorem matrix_sampling_intdim_tail (hnn : 0 < nn)
    (hR₀m : Measurable R₀) (hbd : ∀ ω, ‖R₀ ω‖ ≤ L)
    (hmean : expectation μ R₀ = B)
    (hM₁psd : M₁.PosSemidef) (hM₂psd : M₂.PosSemidef)
    (hM0 : ¬(M₁ = 0 ∧ M₂ = 0))
    (hM₁ : expectation μ (fun ω => R₀ ω * (R₀ ω)ᴴ) ≤ M₁)
    (hM₂ : expectation μ (fun ω => (R₀ ω)ᴴ * R₀ ω) ≤ M₂)
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀ μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ)
    {t : ℝ} (ht : Real.sqrt (max ‖M₁‖ ‖M₂‖) + L / 3 ≤ t) :
    μ.real {ω | t ≤ ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖} ≤
      4 * intdim (Matrix.fromBlocks M₁ 0 0 M₂) *
        Real.exp (-(nn * t ^ 2) / 2 / (max ‖M₁‖ ‖M₂‖ + 2 * L * t / 3)) := by
  classical
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  have hBnorm : ‖B‖ ≤ L := hmean ▸ norm_expectation_le_of_bound hR₀m hbd
  have hL0 : 0 ≤ L := (norm_nonneg B).trans hBnorm
  set mm : ℝ := max ‖M₁‖ ‖M₂‖ with hmmdef
  have hmpos : 0 < mm := by
    rcases (not_and_or.mp hM0) with h | h
    · exact lt_max_of_lt_left (norm_pos_iff.mpr h)
    · exact lt_max_of_lt_right (norm_pos_iff.mpr h)
  have hd1 : 1 ≤ intdim (Matrix.fromBlocks M₁ 0 0 M₂) := one_le_intdim
    (posSemidef_fromBlocks_diag hM₁psd hM₂psd)
    (fun h => hM0 (fromBlocks_diag_eq_zero_iff.mp h))
  have htpos : 0 < t := by
    have h1 : 0 < Real.sqrt mm := Real.sqrt_pos.mpr hmpos
    have h2 : 0 ≤ L / 3 := by positivity
    linarith
  have hDpos : 0 < mm + 2 * L * t / 3 := by
    have h1 : 0 ≤ 2 * L * t / 3 := by positivity
    linarith
  rcases le_or_gt (mm + 2 * L * t / 3) ((nn : ℝ) * t ^ 2) with hcase | hcase
  · -- nonvacuous regime: run the Chapter-6 reduction and the core bound
    set c : ℝ := (nn : ℝ)⁻¹ with hcdef
    have hc0 : 0 ≤ c := by positivity
    have hcpos : 0 < c := by positivity
    set S : Fin nn → Ω → Matrix m n ℂ := fun k ω => c • (R k ω - B)
      with hSdef
    have hSmeas : ∀ k, Measurable (S k) := fun k => by
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      show Measurable fun ω => (c • (R k ω - B)) i j
      have h1 : (fun ω => (c • (R k ω - B)) i j) =
          fun ω => c • (R k ω i j - B i j) := rfl
      rw [h1]
      exact Measurable.const_smul
        (((measurable_entry i j).comp (hmeas k)).sub_const (B i j)) c
    have hRE : ∀ k, expectation μ (R k) = B := fun k =>
      (expectation_of_identDistrib (hid k)).trans hmean
    have hRbd_ae : ∀ k, ∀ᵐ ω ∂μ, ‖R k ω‖ ≤ L := fun k =>
      identDistrib_norm_bound (hid k) hbd
    have hRint : ∀ k, MIntegrable (R k) μ := fun k =>
      MIntegrable.of_bound (hmeas k) L ((hRbd_ae k).mono fun ω h i j =>
        (norm_entry_le_l2_opNorm_rect _ _ _).trans h)
    have hScent : ∀ k, expectation μ (S k) = 0 := by
      intro k
      have h1 := expectation_real_smul (μ := μ) c (fun ω => R k ω - B)
      rw [show S k = fun ω => c • (R k ω - B) from rfl, h1,
        show (fun ω => R k ω - B) =
          fun ω => R k ω - (fun _ : Ω => B) ω from rfl,
        expectation_sub (hRint k) (MIntegrable.const B),
        expectation_const (μ := μ), hRE k, sub_self, smul_zero]
    have hSbd_ae : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ 2 * L / nn := by
      intro k
      filter_upwards [hRbd_ae k] with ω hω
      show ‖c • (R k ω - B)‖ ≤ 2 * L / nn
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
      have h1 : ‖R k ω - B‖ ≤ 2 * L := (norm_sub_le _ _).trans (by linarith)
      calc c * ‖R k ω - B‖ ≤ c * (2 * L) :=
            mul_le_mul_of_nonneg_left h1 hc0
      _ = 2 * L / nn := by
            rw [hcdef]
            field_simp
    have hL' : (0 : ℝ) ≤ 2 * L / nn := by positivity
    have hSind : ProbabilityTheory.iIndepFun S μ := by
      refine hind.comp (fun k M => c • (M - B)) fun k => ?_
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      show Measurable fun M : Matrix m n ℂ => c • (M i j - B i j)
      exact Measurable.const_smul ((measurable_entry i j).sub_const (B i j)) c
    -- the Loewner variance bounds
    have hV₁sum := sampling_S_var1 (μ := μ) hnn hR₀m hbd hmean hM₁ hid
    have hV₂sum := sampling_S_var2 (μ := μ) hnn hR₀m hbd hmean hM₂ hid
    have hV₁psd' : ((nn : ℝ)⁻¹ • M₁).PosSemidef :=
      posSemidef_smul_nonneg hM₁psd (by positivity)
    have hV₂psd' : ((nn : ℝ)⁻¹ • M₂).PosSemidef :=
      posSemidef_smul_nonneg hM₂psd (by positivity)
    have hV0' : ¬((nn : ℝ)⁻¹ • M₁ = 0 ∧ (nn : ℝ)⁻¹ • M₂ = 0) := by
      rintro ⟨h1, h2⟩
      refine hM0 ⟨?_, ?_⟩
      · rcases smul_eq_zero.mp h1 with h | h
        · exact absurd h (by positivity)
        · exact h
      · rcases smul_eq_zero.mp h2 with h | h
        · exact absurd h (by positivity)
        · exact h
    have hmax : max ‖(nn : ℝ)⁻¹ • M₁‖ ‖(nn : ℝ)⁻¹ • M₂‖ = c * mm := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity :
        (0 : ℝ) < (nn : ℝ)⁻¹), hmmdef, hcdef]
      exact ((monotone_mul_left_of_nonneg hc0).map_max).symm
    have htv' : max ‖(nn : ℝ)⁻¹ • M₁‖ ‖(nn : ℝ)⁻¹ • M₂‖ +
        2 * L / nn * t / 3 ≤ t ^ 2 := by
      rw [hmax]
      have h1 : c * mm + 2 * L / nn * t / 3 =
          (mm + 2 * L * t / 3) / nn := by
        rw [hcdef]
        field_simp
      rw [h1, div_le_iff₀ hnR]
      calc mm + 2 * L * t / 3 ≤ (nn : ℝ) * t ^ 2 := hcase
        _ = t ^ 2 * nn := by ring
    have h := intdim_bernstein_rect_tail_core_ae (μ := μ) hSmeas hSbd_ae hL'
      hScent hSind hV₁psd' hV₂psd' hV0' hV₁sum hV₂sum htpos htv'
    -- rewrite the event, the dimension, and the exponent
    have hsum : ∀ ω, (∑ k, S k ω) = (nn : ℝ)⁻¹ • (∑ k, R k ω) - B := by
      intro ω
      show (∑ k, c • (R k ω - B)) = _
      rw [← Finset.smul_sum,
        show (∑ k, (R k ω - B)) = (∑ k, R k ω) - ∑ _k : Fin nn, B from by
          rw [Finset.sum_sub_distrib],
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub,
        hcdef]
      congr 1
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast hnn.ne' : (nn : ℝ) ≠ 0), one_smul]
    rw [show {ω | t ≤ ‖∑ k, S k ω‖} =
        {ω | t ≤ ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖} from by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [hsum ω]] at h
    rw [intdim_fromBlocks_smul_inv hnn, hmax] at h
    have hexp_eq : -(t ^ 2) / 2 / (c * mm + 2 * L / nn * t / 3) =
        -((nn : ℝ) * t ^ 2) / 2 / (mm + 2 * L * t / 3) := by
      rw [hcdef]
      rw [show (nn : ℝ)⁻¹ * mm + 2 * L / nn * t / 3 =
          (mm + 2 * L * t / 3) / nn from by
        field_simp]
      rw [div_div, div_div, div_eq_div_iff (by positivity) (by
        have h2 : (0 : ℝ) < mm + 2 * L * t / 3 := hDpos
        positivity)]
      field_simp
    rw [hexp_eq] at h
    exact h
  · -- vacuous regime: the right-hand side exceeds one
    have hP1 : μ.real {ω | t ≤ ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖} ≤ 1 := by
      have h := measureReal_mono (μ := μ)
        (Set.subset_univ {ω | t ≤ ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖})
      rwa [probReal_univ] at h
    have hexphalf : Real.exp (-(1 : ℝ) / 2) ≤
        Real.exp (-((nn : ℝ) * t ^ 2) / 2 / (mm + 2 * L * t / 3)) := by
      apply Real.exp_le_exp.mpr
      rw [div_div, neg_div, neg_div, neg_le_neg_iff]
      rw [div_le_div_iff₀ (by linarith [hDpos] :
        (0 : ℝ) < 2 * (mm + 2 * L * t / 3)) (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hcase.le, hDpos]
    have hhalf : (1 : ℝ) / 2 ≤ Real.exp (-(1 : ℝ) / 2) := by
      have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h3 : Real.exp (1 / 2) ≤ 2 := by
        nlinarith [Real.exp_pos (1 / 2)]
      have h4 : Real.exp (-(1 : ℝ) / 2) = (Real.exp (1 / 2))⁻¹ := by
        rw [show -(1 : ℝ) / 2 = -(1 / 2) by norm_num, Real.exp_neg]
      rw [h4]
      rw [le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
      calc Real.exp (1 / 2) ≤ 2 := h3
        _ = (1 / 2 : ℝ)⁻¹ := by norm_num
    refine hP1.trans ?_
    have h5 : (1 : ℝ) / 2 ≤
        Real.exp (-((nn : ℝ) * t ^ 2) / 2 / (mm + 2 * L * t / 3)) :=
      hhalf.trans hexphalf
    nlinarith [hd1, h5]

/-- **Book Corollary 7.3.3, expectation bound** (C7-23):

`𝔼‖R̄_n − B‖ ≤ Const·[√(m log(1+d)/n) + L log(1+d)/n]`

with the unspecified `Const` made explicit (`10` and `20` on the two terms,
from Corollary 7.3.2's constant and `L' = 2L/n`).  The source declaration
omits the proof as similar to Corollary 6.2.1.

**Author note.** Lean records explicit coefficients for the source's unspecified
constant and states the nondegeneracy and pointwise-bound regularity used in
the reduction.  See `matrix_sampling_intdim_expectation_ae` for the
source-faithful almost-everywhere counterpart. -/
theorem matrix_sampling_intdim_expectation (hnn : 0 < nn)
    (hR₀m : Measurable R₀) (hbd : ∀ ω, ‖R₀ ω‖ ≤ L)
    (hmean : expectation μ R₀ = B)
    (hM₁psd : M₁.PosSemidef) (hM₂psd : M₂.PosSemidef)
    (hM0 : ¬(M₁ = 0 ∧ M₂ = 0))
    (hM₁ : expectation μ (fun ω => R₀ ω * (R₀ ω)ᴴ) ≤ M₁)
    (hM₂ : expectation μ (fun ω => (R₀ ω)ᴴ * R₀ ω) ≤ M₂)
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k) R₀ μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖ ∂μ ≤
      10 * Real.sqrt (max ‖M₁‖ ‖M₂‖ *
          Real.log (1 + intdim (Matrix.fromBlocks M₁ 0 0 M₂)) / nn) +
        20 * L * Real.log (1 + intdim (Matrix.fromBlocks M₁ 0 0 M₂)) / nn
      := by
  classical
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  have hBnorm : ‖B‖ ≤ L := hmean ▸ norm_expectation_le_of_bound hR₀m hbd
  have hL0 : 0 ≤ L := (norm_nonneg B).trans hBnorm
  set c : ℝ := (nn : ℝ)⁻¹ with hcdef
  have hc0 : 0 ≤ c := by positivity
  set S : Fin nn → Ω → Matrix m n ℂ := fun k ω => c • (R k ω - B)
    with hSdef
  have hSmeas : ∀ k, Measurable (S k) := fun k => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => (c • (R k ω - B)) i j
    have h1 : (fun ω => (c • (R k ω - B)) i j) =
        fun ω => c • (R k ω i j - B i j) := rfl
    rw [h1]
    exact Measurable.const_smul
      (((measurable_entry i j).comp (hmeas k)).sub_const (B i j)) c
  have hRE : ∀ k, expectation μ (R k) = B := fun k =>
    (expectation_of_identDistrib (hid k)).trans hmean
  have hRbd_ae : ∀ k, ∀ᵐ ω ∂μ, ‖R k ω‖ ≤ L := fun k =>
    identDistrib_norm_bound (hid k) hbd
  have hRint : ∀ k, MIntegrable (R k) μ := fun k =>
    MIntegrable.of_bound (hmeas k) L ((hRbd_ae k).mono fun ω h i j =>
      (norm_entry_le_l2_opNorm_rect _ _ _).trans h)
  have hScent : ∀ k, expectation μ (S k) = 0 := by
    intro k
    have h1 := expectation_real_smul (μ := μ) c (fun ω => R k ω - B)
    rw [show S k = fun ω => c • (R k ω - B) from rfl, h1,
      show (fun ω => R k ω - B) =
        fun ω => R k ω - (fun _ : Ω => B) ω from rfl,
      expectation_sub (hRint k) (MIntegrable.const B),
      expectation_const (μ := μ), hRE k, sub_self, smul_zero]
  have hSbd_ae : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ 2 * L / nn := by
    intro k
    filter_upwards [hRbd_ae k] with ω hω
    show ‖c • (R k ω - B)‖ ≤ 2 * L / nn
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    have h1 : ‖R k ω - B‖ ≤ 2 * L := (norm_sub_le _ _).trans (by linarith)
    calc c * ‖R k ω - B‖ ≤ c * (2 * L) :=
          mul_le_mul_of_nonneg_left h1 hc0
    _ = 2 * L / nn := by
          rw [hcdef]
          field_simp
  have hL' : (0 : ℝ) ≤ 2 * L / nn := by positivity
  have hSind : ProbabilityTheory.iIndepFun S μ := by
    refine hind.comp (fun k M => c • (M - B)) fun k => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun M : Matrix m n ℂ => c • (M i j - B i j)
    exact Measurable.const_smul ((measurable_entry i j).sub_const (B i j)) c
  have hV₁sum := sampling_S_var1 (μ := μ) hnn hR₀m hbd hmean hM₁ hid
  have hV₂sum := sampling_S_var2 (μ := μ) hnn hR₀m hbd hmean hM₂ hid
  have hV₁psd' : ((nn : ℝ)⁻¹ • M₁).PosSemidef :=
    posSemidef_smul_nonneg hM₁psd (by positivity)
  have hV₂psd' : ((nn : ℝ)⁻¹ • M₂).PosSemidef :=
    posSemidef_smul_nonneg hM₂psd (by positivity)
  have hV0' : ¬((nn : ℝ)⁻¹ • M₁ = 0 ∧ (nn : ℝ)⁻¹ • M₂ = 0) := by
    rintro ⟨h1, h2⟩
    refine hM0 ⟨?_, ?_⟩
    · rcases smul_eq_zero.mp h1 with h | h
      · exact absurd h (by positivity)
      · exact h
    · rcases smul_eq_zero.mp h2 with h | h
      · exact absurd h (by positivity)
      · exact h
  have h := intdim_bernstein_rect_expectation (μ := μ) hSmeas hSbd_ae hL'
    hScent hSind hV₁psd' hV₂psd' hV0' hV₁sum hV₂sum
  -- rewrite the estimator, the dimension, and the parameters
  have hsum : ∀ ω, (∑ k, S k ω) = (nn : ℝ)⁻¹ • (∑ k, R k ω) - B := by
    intro ω
    show (∑ k, c • (R k ω - B)) = _
    rw [← Finset.smul_sum,
      show (∑ k, (R k ω - B)) = (∑ k, R k ω) - ∑ _k : Fin nn, B from by
        rw [Finset.sum_sub_distrib],
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub,
      hcdef]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hnn.ne' : (nn : ℝ) ≠ 0), one_smul]
  rw [show (fun ω => ‖∑ k, S k ω‖) =
      fun ω => ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖ from
    funext fun ω => by rw [hsum ω]] at h
  rw [intdim_fromBlocks_smul_inv hnn] at h
  have hmax : max ‖(nn : ℝ)⁻¹ • M₁‖ ‖(nn : ℝ)⁻¹ • M₂‖ =
      c * max ‖M₁‖ ‖M₂‖ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity :
      (0 : ℝ) < (nn : ℝ)⁻¹), hcdef]
    exact ((monotone_mul_left_of_nonneg hc0).map_max).symm
  rw [hmax] at h
  refine h.trans (le_of_eq ?_)
  set d : ℝ := intdim (Matrix.fromBlocks M₁ 0 0 M₂)
  have h1 : c * max ‖M₁‖ ‖M₂‖ * Real.log (1 + d) =
      max ‖M₁‖ ‖M₂‖ * Real.log (1 + d) / nn := by
    rw [hcdef]
    ring
  rw [mul_add, h1]
  have h2 : 10 * (2 * L / nn * Real.log (1 + d)) =
      20 * L * Real.log (1 + d) / nn := by
    ring
  rw [h2]

end SamplingEstimator

section RandomizedMultiplication

variable {d₁ d₂ N : ℕ}
variable {B : Matrix (Fin d₁) (Fin N) ℂ} {C : Matrix (Fin N) (Fin d₂) ℂ}

/-- **Book §7.3.3, recalled display (second line)** (C7-24): the Loewner
second-moment bound `𝔼(RR*) ≼ (‖B‖_F² + ‖C‖_F²)·BB*` — under the §7.3.3
normalization this is "`𝔼(RR*) ≼ 2·asr·BB*`".  The §6.4.3 computation,
extracted at the Loewner level (Chapter 6 packaged only its norm). -/
lemma matmul_var1_le (hB : B ≠ 0) {J : Ω → Fin N} (hJ : Measurable J)
    (hJlaw : ∀ j, μ.real (J ⁻¹' {j}) = matmulProb B C j) :
    expectation μ (fun ω => matmulValue B C (J ω) *
        (matmulValue B C (J ω))ᴴ) ≤
      (frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2) • (B * Bᴴ) := by
  classical
  set S : ℝ := frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2 with hSdef
  have hF := frobeniusNorm_pos hB
  have hS : 0 < S := by
    have := frobeniusNorm_nonneg C
    nlinarith
  have ha1le : ∀ j, matmulProb B C j *
      ((matmulProb B C j)⁻¹ ^ 2 * rowNormSq C j) ≤ S := by
    intro j
    by_cases hp : matmulProb B C j = 0
    · rw [hp, zero_mul]
      exact hS.le
    · have hppos : 0 < matmulProb B C j :=
        lt_of_le_of_ne (matmulProb_nonneg B C j) (Ne.symm hp)
      have hval : matmulProb B C j *
          ((matmulProb B C j)⁻¹ ^ 2 * rowNormSq C j) =
          rowNormSq C j / matmulProb B C j := by
        field_simp
      rw [hval, div_le_iff₀ hppos, matmulProb, ← hSdef, mul_div_assoc',
        mul_comm S, mul_div_assoc, div_self hS.ne', mul_one]
      linarith [colNormSq_nonneg B j]
  calc expectation μ (fun ω => matmulValue B C (J ω) *
      (matmulValue B C (J ω))ᴴ)
      = ∑ j, (μ.real (J ⁻¹' {j})) •
          (matmulValue B C j * (matmulValue B C j)ᴴ) :=
        expectation_discrete (μ := μ) hJ (measurable_of_countable _)
          (fun j => matmulValue B C j * (matmulValue B C j)ᴴ)
    _ = ∑ j, (matmulProb B C j *
          ((matmulProb B C j)⁻¹ ^ 2 * rowNormSq C j)) • colGram B j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hJlaw j, matmulValue_mul_conjTranspose, smul_smul]
    _ ≤ ∑ j, S • colGram B j :=
        sum_loewner_mono Finset.univ fun j _ =>
          smul_le_smul_of_posSemidef (posSemidef_colGram B j) (ha1le j)
    _ = S • (B * Bᴴ) := by
        rw [← Finset.smul_sum, sum_colGram]

/-- **Book §7.3.3, recalled display (third line)** (C7-24): the mirror
Loewner bound `𝔼(R*R) ≼ (‖B‖_F² + ‖C‖_F²)·C*C`. -/
lemma matmul_var2_le (hB : B ≠ 0) {J : Ω → Fin N} (hJ : Measurable J)
    (hJlaw : ∀ j, μ.real (J ⁻¹' {j}) = matmulProb B C j) :
    expectation μ (fun ω => (matmulValue B C (J ω))ᴴ *
        matmulValue B C (J ω)) ≤
      (frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2) • (Cᴴ * C) := by
  classical
  set S : ℝ := frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2 with hSdef
  have hF := frobeniusNorm_pos hB
  have hS : 0 < S := by
    have := frobeniusNorm_nonneg C
    nlinarith
  have ha2le : ∀ j, matmulProb B C j *
      ((matmulProb B C j)⁻¹ ^ 2 * colNormSq B j) ≤ S := by
    intro j
    by_cases hp : matmulProb B C j = 0
    · rw [hp, zero_mul]
      exact hS.le
    · have hppos : 0 < matmulProb B C j :=
        lt_of_le_of_ne (matmulProb_nonneg B C j) (Ne.symm hp)
      have hval : matmulProb B C j *
          ((matmulProb B C j)⁻¹ ^ 2 * colNormSq B j) =
          colNormSq B j / matmulProb B C j := by
        field_simp
      rw [hval, div_le_iff₀ hppos, matmulProb, ← hSdef, mul_div_assoc',
        mul_comm S, mul_div_assoc, div_self hS.ne', mul_one]
      linarith [rowNormSq_nonneg C j]
  calc expectation μ (fun ω => (matmulValue B C (J ω))ᴴ *
      matmulValue B C (J ω))
      = ∑ j, (μ.real (J ⁻¹' {j})) •
          ((matmulValue B C j)ᴴ * matmulValue B C j) :=
        expectation_discrete (μ := μ) hJ (measurable_of_countable _)
          (fun j => (matmulValue B C j)ᴴ * matmulValue B C j)
    _ = ∑ j, (matmulProb B C j *
          ((matmulProb B C j)⁻¹ ^ 2 * colNormSq B j)) • rowGram C j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hJlaw j, conjTranspose_mul_matmulValue, smul_smul]
    _ ≤ ∑ j, S • rowGram C j :=
        sum_loewner_mono Finset.univ fun j _ =>
          smul_le_smul_of_posSemidef (posSemidef_rowGram C j) (ha2le j)
    _ = S • (Cᴴ * C) := by
        rw [← Finset.smul_sum, sum_rowGram]

/-- **Book §7.3.3, final displays** (C7-25/C7-26/C7-27): under the
normalization `‖B‖ = ‖C‖ = 1`, with `asr = (srank(B) + srank(C))/2`,

`𝔼‖R̄_n − BC‖ ≤ 20·√(asr·log(1+asr)/n) + 40·asr·log(1+asr)/n`

— Corollary 7.3.3 applied with `M₁ = 2·asr·BB*`, `M₂ = 2·asr·C*C`, using
`d ≤ intdim(M₁) + intdim(M₂) = srank(B) + srank(C) = 2·asr`
(using the stable-rank identities),
`m = 2·asr`, `L = asr`, and `log(1+2·asr) ≤ 2·log(1+asr)`; the source's
`Const` is made explicit.  Explicit source displays.

**Author note.** The source leaves `Const` unspecified; Lean records the
coefficients `20` and `40`. -/
theorem matmul_intdim_error_bound
    (hBn : ‖B‖ = 1) (hCn : ‖C‖ = 1) (hd₁ : 0 < d₁) {nn : ℕ} (hnn : 0 < nn)
    {J : Ω → Fin N} (hJ : Measurable J)
    (hJlaw : ∀ j, μ.real (J ⁻¹' {j}) = matmulProb B C j)
    {R : Fin nn → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k)
      (fun ω => matmulValue B C (J ω)) μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B * C‖ ∂μ ≤
      20 * Real.sqrt ((stableRank B + stableRank C) / 2 *
          Real.log (1 + (stableRank B + stableRank C) / 2) / nn) +
        40 * ((stableRank B + stableRank C) / 2) *
          Real.log (1 + (stableRank B + stableRank C) / 2) / nn := by
  classical
  haveI : Nonempty (Fin d₁ ⊕ Fin d₂) := ⟨Sum.inl ⟨0, hd₁⟩⟩
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  have hB : B ≠ 0 := by
    intro h
    rw [h, norm_zero] at hBn
    norm_num at hBn
  have hsB : stableRank B = frobeniusNorm B ^ 2 := by
    rw [stableRank, hBn]
    norm_num
  have hsC : stableRank C = frobeniusNorm C ^ 2 := by
    rw [stableRank, hCn]
    norm_num
  set S : ℝ := frobeniusNorm B ^ 2 + frobeniusNorm C ^ 2 with hSdef
  have hF := frobeniusNorm_pos hB
  have hS : 0 < S := by
    have := frobeniusNorm_nonneg C
    nlinarith
  have hasr : (stableRank B + stableRank C) / 2 = S / 2 := by
    rw [hsB, hsC]
  have hR₀m : Measurable fun ω => matmulValue B C (J ω) :=
    (measurable_of_countable (matmulValue B C)).comp hJ
  have hbd : ∀ ω, ‖matmulValue B C (J ω)‖ ≤ S / 2 := fun ω =>
    matmul_norm_le hB (J ω)
  have hmean := expectation_matmulEstimator (μ := μ) hB hJ hJlaw
  have hM₁psd : (S • (B * Bᴴ)).PosSemidef :=
    posSemidef_smul_nonneg (Matrix.posSemidef_self_mul_conjTranspose B) hS.le
  have hM₂psd : (S • (Cᴴ * C)).PosSemidef :=
    posSemidef_smul_nonneg (Matrix.posSemidef_conjTranspose_mul_self C) hS.le
  have hM0 : ¬(S • (B * Bᴴ) = 0 ∧ S • (Cᴴ * C) = 0) := by
    rintro ⟨h1, _⟩
    rcases smul_eq_zero.mp h1 with h | h
    · exact hS.ne' h
    · have h3 : ‖B‖ ^ 2 = 0 := by
        rw [(l2_opNorm_sq_eq B).1, h, norm_zero]
      rw [hBn] at h3
      norm_num at h3
  have hM₁le := matmul_var1_le (μ := μ) hB hJ hJlaw
  have hM₂le := matmul_var2_le (μ := μ) hB hJ hJlaw
  have h := matrix_sampling_intdim_expectation (μ := μ) hnn hR₀m hbd hmean
    hM₁psd hM₂psd hM0 hM₁le hM₂le hmeas hid hind
  -- identify the parameters
  have hmm : max ‖S • (B * Bᴴ)‖ ‖S • (Cᴴ * C)‖ = S := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hS,
      ← (l2_opNorm_sq_eq B).1, ← (l2_opNorm_sq_eq C).2, hBn, hCn]
    norm_num
  set d : ℝ := intdim (Matrix.fromBlocks (S • (B * Bᴴ)) 0 0 (S • (Cᴴ * C)))
    with hddef
  have hd0 : 0 ≤ d := intdim_nonneg (posSemidef_fromBlocks_diag hM₁psd hM₂psd)
  have hd_le : d ≤ S := by
    rw [hddef]
    refine (intdim_fromBlocks_le_add hM₁psd hM₂psd).trans ?_
    rw [intdim_smul hS, intdim_smul hS, intdim_gram_eq_stableRank,
      intdim_gram_conjTranspose_eq_stableRank, hsB, hsC]
  have hlogd : Real.log (1 + d) ≤ 2 * Real.log (1 + S / 2) := by
    calc Real.log (1 + d) ≤ Real.log (1 + S) :=
        Real.log_le_log (by linarith) (by linarith)
      _ ≤ 2 * Real.log (1 + S / 2) := by
          rw [show (2 : ℝ) * Real.log (1 + S / 2) =
              Real.log ((1 + S / 2) ^ 2) from by
            rw [Real.log_pow]
            push_cast
            ring]
          apply Real.log_le_log (by linarith)
          nlinarith [hS]
  have hloga : 0 ≤ Real.log (1 + S / 2) := Real.log_nonneg (by linarith)
  rw [hmm] at h
  refine h.trans ?_
  rw [hasr]
  -- the square-root term
  have hsq : Real.sqrt (S * Real.log (1 + d) / nn) ≤
      2 * Real.sqrt (S / 2 * Real.log (1 + S / 2) / nn) := by
    rw [show (2 : ℝ) * Real.sqrt (S / 2 * Real.log (1 + S / 2) / nn) =
        Real.sqrt (4 * (S / 2 * Real.log (1 + S / 2) / nn)) from by
      rw [show (4 : ℝ) * (S / 2 * Real.log (1 + S / 2) / nn) =
          2 ^ 2 * (S / 2 * Real.log (1 + S / 2) / nn) from by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    have hnum : S * Real.log (1 + d) ≤
        4 * (S / 2 * Real.log (1 + S / 2)) := by
      calc S * Real.log (1 + d) ≤ S * (2 * Real.log (1 + S / 2)) :=
          mul_le_mul_of_nonneg_left hlogd hS.le
        _ = 4 * (S / 2 * Real.log (1 + S / 2)) := by ring
    calc S * Real.log (1 + d) / nn ≤
        4 * (S / 2 * Real.log (1 + S / 2)) / nn := by gcongr
      _ = 4 * (S / 2 * Real.log (1 + S / 2) / nn) := by ring
  -- the linear term
  have hlin : 20 * (S / 2) * Real.log (1 + d) / nn ≤
      40 * (S / 2) * Real.log (1 + S / 2) / nn := by
    rw [div_le_div_iff_of_pos_right hnR]
    calc 20 * (S / 2) * Real.log (1 + d) ≤
        20 * (S / 2) * (2 * Real.log (1 + S / 2)) := by
          apply mul_le_mul_of_nonneg_left hlogd
          positivity
      _ = 40 * (S / 2) * Real.log (1 + S / 2) := by ring
  calc 10 * Real.sqrt (S * Real.log (1 + d) / nn) +
      20 * (S / 2) * Real.log (1 + d) / nn
      ≤ 10 * (2 * Real.sqrt (S / 2 * Real.log (1 + S / 2) / nn)) +
        40 * (S / 2) * Real.log (1 + S / 2) / nn := by
        refine add_le_add ?_ hlin
        exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 20 * Real.sqrt (S / 2 * Real.log (1 + S / 2) / nn) +
        40 * (S / 2) * Real.log (1 + S / 2) / nn := by ring

/-- **Book §7.3.3, sample-count display** (C7-28): "if the number `n` of
samples satisfies `n ≥ ε⁻²·asr·log(1 + asr)`, then the error satisfies
`𝔼‖R̄_n − BC‖ ≤ Const·(ε + ε²)`" — with the explicit constants of
`matmul_intdim_error_bound`: `𝔼‖R̄_n − BC‖ ≤ 20ε + 40ε²`.  Explicit source
displays.

**Author note.** The coefficients `20` and `40` instantiate the source's
unspecified constant. -/
theorem matmul_intdim_sample_cost
    (hBn : ‖B‖ = 1) (hCn : ‖C‖ = 1) (hd₁ : 0 < d₁) {nn : ℕ} (hnn : 0 < nn)
    {J : Ω → Fin N} (hJ : Measurable J)
    (hJlaw : ∀ j, μ.real (J ⁻¹' {j}) = matmulProb B C j)
    {R : Fin nn → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (R k)
      (fun ω => matmulValue B C (J ω)) μ μ)
    (hind : ProbabilityTheory.iIndepFun R μ)
    {ε : ℝ} (hε : 0 < ε)
    (hcost : ε⁻¹ ^ 2 * ((stableRank B + stableRank C) / 2) *
      Real.log (1 + (stableRank B + stableRank C) / 2) ≤ nn) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B * C‖ ∂μ ≤
      20 * ε + 40 * ε ^ 2 := by
  have hnR : (0 : ℝ) < nn := by exact_mod_cast hnn
  set a : ℝ := (stableRank B + stableRank C) / 2 with hadef
  have hB : B ≠ 0 := by
    intro h
    rw [h, norm_zero] at hBn
    norm_num at hBn
  have hC : C ≠ 0 := by
    intro h
    rw [h, norm_zero] at hCn
    norm_num at hCn
  have ha1 : 1 ≤ a := by
    have h1 := one_le_stableRank hB
    have h2 := one_le_stableRank hC
    rw [hadef]
    linarith
  have hla : 0 ≤ Real.log (1 + a) := Real.log_nonneg (by linarith)
  have hX : a * Real.log (1 + a) / nn ≤ ε ^ 2 := by
    rw [div_le_iff₀ hnR]
    have h0 : ε ^ 2 * (ε⁻¹ ^ 2 * a * Real.log (1 + a)) =
        a * Real.log (1 + a) := by
      field_simp
    calc a * Real.log (1 + a) =
        ε ^ 2 * (ε⁻¹ ^ 2 * a * Real.log (1 + a)) := h0.symm
      _ ≤ ε ^ 2 * nn :=
          mul_le_mul_of_nonneg_left hcost (by positivity)
  have hsqrt : Real.sqrt (a * Real.log (1 + a) / nn) ≤ ε := by
    calc Real.sqrt (a * Real.log (1 + a) / nn) ≤ Real.sqrt (ε ^ 2) :=
        Real.sqrt_le_sqrt hX
      _ = ε := Real.sqrt_sq hε.le
  have h := matmul_intdim_error_bound (μ := μ) hBn hCn hd₁ hnn hJ hJlaw
    hmeas hid hind
  rw [← hadef] at h
  refine h.trans ?_
  have h3 : 40 * a * Real.log (1 + a) / nn =
      40 * (a * Real.log (1 + a) / nn) := by ring
  have h4 : 40 * (a * Real.log (1 + a) / nn) ≤ 40 * ε ^ 2 :=
    mul_le_mul_of_nonneg_left hX (by norm_num)
  have h5 : 20 * Real.sqrt (a * Real.log (1 + a) / nn) ≤ 20 * ε :=
    mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  rw [h3]
  linarith

end RandomizedMultiplication

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Source-faithful almost-sure counterparts

The Book states support and boundedness hypotheses in the usual almost-sure
sense.  The original declarations above use pointwise hypotheses because the
core matrix-mgf arguments are most convenient in that form.  The theorems in
this final section transfer the pointwise results along measurable null
modifications; no concentration argument is repeated here.
-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

section IntrinsicChernoffAe

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {X : ι → Ω → Matrix n n ℂ} {L : ℝ} {M : Matrix n n ℂ}

/-- Lean implementation helper: measurable replacement of a square matrix by
its Hermitian part when its spectrum lies in `[0,L]`, and by zero otherwise.
This turns almost-sure Chernoff support into pointwise support. -/
noncomputable def chernoffRangeRepresentative (L : ℝ) (B : Matrix n n ℂ) :
    Matrix n n ℂ :=
  if 0 ≤ lambdaMin (isHermitian_hermPart B) ∧
      lambdaMax (isHermitian_hermPart B) ≤ L then hermPart B else 0

/-- Lean implementation helper: measurability of the Chernoff range
representative. -/
lemma measurable_chernoffRangeRepresentative (L : ℝ) :
    Measurable (chernoffRangeRepresentative (n := n) L) := by
  have hmin : Measurable fun B : Matrix n n ℂ =>
      lambdaMin (isHermitian_hermPart B) :=
    measurable_lambdaMin_of_forall continuous_hermPart.measurable
      isHermitian_hermPart
  have hmax : Measurable fun B : Matrix n n ℂ =>
      lambdaMax (isHermitian_hermPart B) :=
    measurable_lambdaMax_of_forall continuous_hermPart.measurable
      isHermitian_hermPart
  have hs : MeasurableSet {B : Matrix n n ℂ |
      0 ≤ lambdaMin (isHermitian_hermPart B) ∧
        lambdaMax (isHermitian_hermPart B) ≤ L} :=
    (hmin measurableSet_Ici).inter (hmax measurableSet_Iic)
  exact Measurable.ite hs continuous_hermPart.measurable measurable_const

/-- Lean implementation helper: the range representative is Hermitian. -/
lemma chernoffRangeRepresentative_isHermitian (L : ℝ) (B : Matrix n n ℂ) :
    (chernoffRangeRepresentative L B).IsHermitian := by
  rw [chernoffRangeRepresentative]
  split_ifs
  · exact isHermitian_hermPart B
  · exact isHermitian_zero

/-- Lean implementation helper: the range representative is positive
semidefinite. -/
lemma chernoffRangeRepresentative_lambdaMin_nonneg (L : ℝ)
    (B : Matrix n n ℂ) :
    0 ≤ lambdaMin (chernoffRangeRepresentative_isHermitian L B) := by
  by_cases h : 0 ≤ lambdaMin (isHermitian_hermPart B) ∧
      lambdaMax (isHermitian_hermPart B) ≤ L
  · have heq : chernoffRangeRepresentative L B = hermPart B := if_pos h
    rw [lambdaMin_congr heq (chernoffRangeRepresentative_isHermitian L B)
      (isHermitian_hermPart B)]
    exact h.1
  · have heq : chernoffRangeRepresentative L B = 0 := if_neg h
    rw [lambdaMin_congr heq (chernoffRangeRepresentative_isHermitian L B)
      isHermitian_zero]
    rw [lambdaMin_zero_matrix isHermitian_zero]

/-- Lean implementation helper: the range representative has upper spectral
edge at most `L`. -/
lemma chernoffRangeRepresentative_lambdaMax_le (hL : 0 ≤ L)
    (B : Matrix n n ℂ) :
    lambdaMax (chernoffRangeRepresentative_isHermitian L B) ≤ L := by
  by_cases h : 0 ≤ lambdaMin (isHermitian_hermPart B) ∧
      lambdaMax (isHermitian_hermPart B) ≤ L
  · have heq : chernoffRangeRepresentative L B = hermPart B := if_pos h
    rw [lambdaMax_congr heq (chernoffRangeRepresentative_isHermitian L B)
      (isHermitian_hermPart B)]
    exact h.2
  · have heq : chernoffRangeRepresentative L B = 0 := if_neg h
    rw [lambdaMax_congr heq (chernoffRangeRepresentative_isHermitian L B)
      isHermitian_zero]
    rw [lambdaMax_zero_matrix isHermitian_zero]
    exact hL

/-- Lean implementation helper: the representative fixes every Hermitian
matrix whose spectrum already lies in `[0,L]`. -/
lemma chernoffRangeRepresentative_eq {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (hmin : 0 ≤ lambdaMin hB)
    (hmax : lambdaMax hB ≤ L) : chernoffRangeRepresentative L B = B := by
  rw [chernoffRangeRepresentative]
  have hp : hermPart B = B := hermPart_of_isHermitian hB
  have hc : 0 ≤ lambdaMin (isHermitian_hermPart B) ∧
      lambdaMax (isHermitian_hermPart B) ≤ L := by
    constructor
    · rw [lambdaMin_congr hp (isHermitian_hermPart B) hB]
      exact hmin
    · rw [lambdaMax_congr hp (isHermitian_hermPart B) hB]
      exact hmax
  rw [if_pos hc, hp]

/-- **Book §7.6, first display of the proof**, with the spectral support
hypotheses interpreted almost surely.  This is the source-faithful sibling of
`chernoff_trace_mgf_bound`; the Hermitian typing witness remains pointwise,
while both spectral-edge bounds hold only almost everywhere. -/
lemma chernoff_trace_mgf_bound_ae
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (hherm k ω) ≤ L)
    (hindep : iIndepFun X μ) (hL : 0 < L) (θ : ℝ) :
    ∫ ω, ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re ∂μ ≤
      ((NormedSpace.exp (gChernoff θ L • ∑ k, expectation μ (X k))).trace).re := by
  classical
  let X' : ι → Ω → Matrix n n ℂ := fun k ω =>
    chernoffRangeRepresentative L (X k ω)
  have hae : ∀ k, X' k =ᵐ[μ] X k := fun k =>
    ((hmin k).and (hmax k)).mono fun ω hω =>
      chernoffRangeRepresentative_eq (hherm k ω) hω.1 hω.2
  have hmeas' : ∀ k, Measurable (X' k) := fun k =>
    (measurable_chernoffRangeRepresentative L).comp (hmeas k)
  have hherm' : ∀ k ω, (X' k ω).IsHermitian := fun k ω =>
    chernoffRangeRepresentative_isHermitian L (X k ω)
  have hmin' : ∀ k ω, 0 ≤ lambdaMin (hherm' k ω) := fun k ω =>
    chernoffRangeRepresentative_lambdaMin_nonneg L (X k ω)
  have hmax' : ∀ k ω, lambdaMax (hherm' k ω) ≤ L := fun k ω =>
    chernoffRangeRepresentative_lambdaMax_le hL.le (X k ω)
  have hindep' : iIndepFun X' μ :=
    hindep.comp (fun _ => chernoffRangeRepresentative L)
      fun _ => measurable_chernoffRangeRepresentative L
  have hmain := chernoff_trace_mgf_bound (μ := μ) hmeas' hherm' hmin' hmax'
    hindep' hL θ
  have hall : ∀ᵐ ω ∂μ, ∀ k, X' k ω = X k ω := (ae_all_iff).mpr hae
  have hsum : (fun ω => ∑ k, X' k ω) =ᵐ[μ] fun ω => ∑ k, X k ω :=
    hall.mono fun ω hω => Finset.sum_congr rfl fun k _ => hω k
  have hlhs : (fun ω =>
      ((NormedSpace.exp (θ • ∑ k, X' k ω)).trace).re) =ᵐ[μ]
      fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re :=
    hsum.mono fun ω hω => by
      have hω' : (∑ k, X' k ω) = ∑ k, X k ω := hω
      change ((NormedSpace.exp (θ • ∑ k, X' k ω)).trace).re =
        ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re
      rw [hω']
  have hEsum : (∑ k, expectation μ (X' k)) =
      ∑ k, expectation μ (X k) :=
    Finset.sum_congr rfl fun k _ => expectation_congr_ae (hae k)
  rwa [integral_congr_ae hlhs, hEsum] at hmain

/-- **Book §7.6, display (7.6.2)** with almost-sure spectral support.  This
is the source-faithful sibling of `chernoff_expected_trace_bound`. -/
lemma chernoff_expected_trace_bound_ae
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (hherm k ω) ≤ L)
    (hindep : iIndepFun X μ) (hL : 0 < L)
    {θ : ℝ} (hθ : 0 < θ) (hMpsd : M.PosSemidef)
    (hM : (∑ k, expectation μ (X k)) ≤ M) :
    ∫ ω, (((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
        (Fintype.card n : ℝ)) ∂μ ≤
      intdim M * Real.exp (gChernoff θ L * ‖M‖) := by
  classical
  let X' : ι → Ω → Matrix n n ℂ := fun k ω =>
    chernoffRangeRepresentative L (X k ω)
  have hae : ∀ k, X' k =ᵐ[μ] X k := fun k =>
    ((hmin k).and (hmax k)).mono fun ω hω =>
      chernoffRangeRepresentative_eq (hherm k ω) hω.1 hω.2
  have hmeas' : ∀ k, Measurable (X' k) := fun k =>
    (measurable_chernoffRangeRepresentative L).comp (hmeas k)
  have hherm' : ∀ k ω, (X' k ω).IsHermitian := fun k ω =>
    chernoffRangeRepresentative_isHermitian L (X k ω)
  have hmin' : ∀ k ω, 0 ≤ lambdaMin (hherm' k ω) := fun k ω =>
    chernoffRangeRepresentative_lambdaMin_nonneg L (X k ω)
  have hmax' : ∀ k ω, lambdaMax (hherm' k ω) ≤ L := fun k ω =>
    chernoffRangeRepresentative_lambdaMax_le hL.le (X k ω)
  have hindep' : iIndepFun X' μ :=
    hindep.comp (fun _ => chernoffRangeRepresentative L)
      fun _ => measurable_chernoffRangeRepresentative L
  have hEsum : (∑ k, expectation μ (X' k)) =
      ∑ k, expectation μ (X k) :=
    Finset.sum_congr rfl fun k _ => expectation_congr_ae (hae k)
  have hmain := chernoff_expected_trace_bound (μ := μ) hmeas' hherm' hmin'
    hmax' hindep' hL hθ hMpsd (hEsum.symm ▸ hM)
  have hall : ∀ᵐ ω ∂μ, ∀ k, X' k ω = X k ω := (ae_all_iff).mpr hae
  have hsum : (fun ω => ∑ k, X' k ω) =ᵐ[μ] fun ω => ∑ k, X k ω :=
    hall.mono fun ω hω => Finset.sum_congr rfl fun k _ => hω k
  have hlhs : (fun ω =>
      (((NormedSpace.exp (θ • ∑ k, X' k ω)).trace).re -
        (Fintype.card n : ℝ))) =ᵐ[μ]
      fun ω => (((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
        (Fintype.card n : ℝ)) := hsum.mono fun ω hω => by
          have hω' : (∑ k, X' k ω) = ∑ k, X k ω := hω
          change ((NormedSpace.exp (θ • ∑ k, X' k ω)).trace).re -
            (Fintype.card n : ℝ) =
            ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
              (Fintype.card n : ℝ)
          rw [hω']
  rwa [integral_congr_ae hlhs] at hmain

/-- **Book Theorem 7.2.1, equation (7.2.2)** with the summand spectral
support interpreted almost surely.  This is the source-faithful sibling of
`intdim_chernoff_tail`. -/
theorem intdim_chernoff_tail_ae
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (hherm k ω) ≤ L)
    (hindep : iIndepFun X μ) (hL : 0 < L)
    (hMpsd : M.PosSemidef) (hM0 : M ≠ 0)
    (hM : (∑ k, expectation μ (X k)) ≤ M)
    {ε : ℝ} (hε : L / lambdaMax hMpsd.1 ≤ ε) :
    μ.real {ω | (1 + ε) * lambdaMax hMpsd.1 ≤
        lambdaMax (isHermitian_matsum Finset.univ fun k => hherm k ω)} ≤
      2 * intdim M *
        (Real.exp ε / (1 + ε) ^ (1 + ε)) ^ (lambdaMax hMpsd.1 / L) := by
  classical
  let X' : ι → Ω → Matrix n n ℂ := fun k ω =>
    chernoffRangeRepresentative L (X k ω)
  have hae : ∀ k, X' k =ᵐ[μ] X k := fun k =>
    ((hmin k).and (hmax k)).mono fun ω hω =>
      chernoffRangeRepresentative_eq (hherm k ω) hω.1 hω.2
  have hmeas' : ∀ k, Measurable (X' k) := fun k =>
    (measurable_chernoffRangeRepresentative L).comp (hmeas k)
  have hherm' : ∀ k ω, (X' k ω).IsHermitian := fun k ω =>
    chernoffRangeRepresentative_isHermitian L (X k ω)
  have hmin' : ∀ k ω, 0 ≤ lambdaMin (hherm' k ω) := fun k ω =>
    chernoffRangeRepresentative_lambdaMin_nonneg L (X k ω)
  have hmax' : ∀ k ω, lambdaMax (hherm' k ω) ≤ L := fun k ω =>
    chernoffRangeRepresentative_lambdaMax_le hL.le (X k ω)
  have hindep' : iIndepFun X' μ :=
    hindep.comp (fun _ => chernoffRangeRepresentative L)
      fun _ => measurable_chernoffRangeRepresentative L
  have hEsum : (∑ k, expectation μ (X' k)) =
      ∑ k, expectation μ (X k) :=
    Finset.sum_congr rfl fun k _ => expectation_congr_ae (hae k)
  have hmain := intdim_chernoff_tail (μ := μ) hmeas' hherm' hmin' hmax'
    hindep' hL hMpsd hM0 (hEsum.symm ▸ hM) hε
  have hall : ∀ᵐ ω ∂μ, ∀ k, X' k ω = X k ω := (ae_all_iff).mpr hae
  have hsum : (fun ω => ∑ k, X' k ω) =ᵐ[μ] fun ω => ∑ k, X k ω :=
    hall.mono fun ω hω => Finset.sum_congr rfl fun k _ => hω k
  have hevent : {ω | (1 + ε) * lambdaMax hMpsd.1 ≤
      lambdaMax (isHermitian_matsum Finset.univ fun k => hherm' k ω)} =ᵐ[μ]
      {ω | (1 + ε) * lambdaMax hMpsd.1 ≤
        lambdaMax (isHermitian_matsum Finset.univ fun k => hherm k ω)} :=
    hsum.mono fun ω hω => by
      have hω' : (∑ k, X' k ω) = ∑ k, X k ω := hω
      change ((1 + ε) * lambdaMax hMpsd.1 ≤
        lambdaMax (isHermitian_matsum Finset.univ fun k => hherm' k ω)) =
        ((1 + ε) * lambdaMax hMpsd.1 ≤
          lambdaMax (isHermitian_matsum Finset.univ fun k => hherm k ω))
      rw [lambdaMax_congr hω'
        (isHermitian_matsum Finset.univ fun k => hherm' k ω)
        (isHermitian_matsum Finset.univ fun k => hherm k ω)]
  rwa [measureReal_congr hevent] at hmain

/-- **Book Theorem 7.2.1, equation (7.2.1)** with the summand spectral
support interpreted almost surely.  This is the source-faithful sibling of
`intdim_chernoff_expectation`. -/
theorem intdim_chernoff_expectation_ae
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (hherm k ω) ≤ L)
    (hindep : iIndepFun X μ) (hL : 0 < L)
    (hMpsd : M.PosSemidef) (hM0 : M ≠ 0)
    (hM : (∑ k, expectation μ (X k)) ≤ M) {θ : ℝ} (hθ : 0 < θ) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ fun k => hherm k ω) ∂μ ≤
      (Real.exp θ - 1) / θ * lambdaMax hMpsd.1 +
        L * Real.log (2 * intdim M) / θ := by
  classical
  let X' : ι → Ω → Matrix n n ℂ := fun k ω =>
    chernoffRangeRepresentative L (X k ω)
  have hae : ∀ k, X' k =ᵐ[μ] X k := fun k =>
    ((hmin k).and (hmax k)).mono fun ω hω =>
      chernoffRangeRepresentative_eq (hherm k ω) hω.1 hω.2
  have hmeas' : ∀ k, Measurable (X' k) := fun k =>
    (measurable_chernoffRangeRepresentative L).comp (hmeas k)
  have hherm' : ∀ k ω, (X' k ω).IsHermitian := fun k ω =>
    chernoffRangeRepresentative_isHermitian L (X k ω)
  have hmin' : ∀ k ω, 0 ≤ lambdaMin (hherm' k ω) := fun k ω =>
    chernoffRangeRepresentative_lambdaMin_nonneg L (X k ω)
  have hmax' : ∀ k ω, lambdaMax (hherm' k ω) ≤ L := fun k ω =>
    chernoffRangeRepresentative_lambdaMax_le hL.le (X k ω)
  have hindep' : iIndepFun X' μ :=
    hindep.comp (fun _ => chernoffRangeRepresentative L)
      fun _ => measurable_chernoffRangeRepresentative L
  have hEsum : (∑ k, expectation μ (X' k)) =
      ∑ k, expectation μ (X k) :=
    Finset.sum_congr rfl fun k _ => expectation_congr_ae (hae k)
  have hmain := intdim_chernoff_expectation (μ := μ) hmeas' hherm' hmin'
    hmax' hindep' hL hMpsd hM0 (hEsum.symm ▸ hM) hθ
  have hall : ∀ᵐ ω ∂μ, ∀ k, X' k ω = X k ω := (ae_all_iff).mpr hae
  have hsum : (fun ω => ∑ k, X' k ω) =ᵐ[μ] fun ω => ∑ k, X k ω :=
    hall.mono fun ω hω => Finset.sum_congr rfl fun k _ => hω k
  have hint : (fun ω =>
      lambdaMax (isHermitian_matsum Finset.univ fun k => hherm' k ω)) =ᵐ[μ]
      fun ω => lambdaMax (isHermitian_matsum Finset.univ fun k => hherm k ω) :=
    hsum.mono fun ω hω => by
      have hω' : (∑ k, X' k ω) = ∑ k, X k ω := hω
      exact lambdaMax_congr hω'
        (isHermitian_matsum Finset.univ fun k => hherm' k ω)
        (isHermitian_matsum Finset.univ fun k => hherm k ω)
  rwa [integral_congr_ae hint] at hmain

end IntrinsicChernoffAe

section IntrinsicColumnBernoulli

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [Nonempty m] [Nonempty n] [IsProbabilityMeasure μ]

/-- **Book §7.2.2, final display** with the Bernoulli support interpreted
almost surely.  This is the source-faithful sibling of
`intdim_column_submatrix_upper`; its only support hypothesis is `IsBernoulli`.
-/
theorem intdim_column_submatrix_upper_of_isBernoulli
    (B : Matrix m n ℂ) (hB : B ≠ 0) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 < q) {δ : n → Ω → ℝ}
    (hmeas : ∀ k, Measurable (δ k)) (hlaw : ∀ k, IsBernoulli q (δ k) μ)
    (hind : iIndepFun δ μ) :
    ∫ ω, ‖columnSubmatrix B δ ω‖ ^ 2 ∂μ ≤
      1.72 * (q * ‖B‖ ^ 2) +
        Real.log (2 * stableRank B) *
          Finset.univ.sup' Finset.univ_nonempty (colNormSq B) := by
  let δ' : n → Ω → ℝ := fun k ω => bernoulliRepresentative (δ k ω)
  have hm' : ∀ k, Measurable (δ' k) := fun k =>
    measurable_bernoulliRepresentative.comp (hmeas k)
  have hl' : ∀ k, IsBernoulli q (δ' k) μ := fun k =>
    isBernoulli_bernoulliRepresentative hq (hmeas k) (hlaw k)
  have hi' : iIndepFun δ' μ :=
    iIndepFun_bernoulliRepresentative hq hmeas hlaw hind
  have hr' : ∀ k ω, δ' k ω = 0 ∨ δ' k ω = 1 := fun k ω =>
    bernoulliRepresentative_range (δ k ω)
  have hmain := intdim_column_submatrix_upper (μ := μ) B hB hq hq0 hm' hl' hr' hi'
  have hall := bernoulliRepresentative_all_ae hq hmeas hlaw
  have hint : (fun ω => ‖columnSubmatrix B δ' ω‖ ^ 2) =ᵐ[μ]
      fun ω => ‖columnSubmatrix B δ ω‖ ^ 2 := by
    filter_upwards [hall] with ω hω
    rw [columnSubmatrix_congr_values B hω]
  rwa [integral_congr_ae hint] at hmain

/-- Totalized strengthening of the §7.2.2 estimate, including `B = 0` and
`q = 0`.  It extends `intdim_column_submatrix_upper` (and its law-only sibling
`intdim_column_submatrix_upper_of_isBernoulli`) to these degenerate corners.
They are mathematically valid under Lean's totalized `intdim`/`log`
conventions, but are not claimed as literal source-domain cases of the Book
display. -/
theorem intdim_column_submatrix_upper_totalized
    (B : Matrix m n ℂ) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    {δ : n → Ω → ℝ} (hmeas : ∀ k, Measurable (δ k))
    (hlaw : ∀ k, IsBernoulli q (δ k) μ) (hind : iIndepFun δ μ) :
    ∫ ω, ‖columnSubmatrix B δ ω‖ ^ 2 ∂μ ≤
      1.72 * (q * ‖B‖ ^ 2) +
        Real.log (2 * stableRank B) *
          Finset.univ.sup' Finset.univ_nonempty (colNormSq B) := by
  by_cases hB : B = 0
  · subst B
    simp [columnSubmatrix, colNormSq, stableRank]
  by_cases hq0' : q = 0
  · subst q
    have hzero : ∀ k, δ k =ᵐ[μ] 0 := by
      intro k
      have hrange := ae_range_isBernoulli
        (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num) (hmeas k) (hlaw k)
      have hint : Integrable (δ k) μ := integrable_isBernoulli
        (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num) (hmeas k) (hlaw k)
        measurable_id
      have hnonneg : 0 ≤ᵐ[μ] δ k := hrange.mono fun ω hω => by
        rcases hω with hω | hω <;> simp [hω]
      have hi : ∫ ω, δ k ω ∂μ = 0 := integral_id_isBernoulli
        (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num) (hmeas k) (hlaw k)
      exact (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hi
    have hall : ∀ᵐ ω ∂μ, ∀ k, δ k ω = 0 := (ae_all_iff).mpr hzero
    have hlhs : (fun ω => ‖columnSubmatrix B δ ω‖ ^ 2) =ᵐ[μ] 0 := by
      filter_upwards [hall] with ω hω
      simp [columnSubmatrix, hω]
    rw [integral_congr_ae hlhs]
    simp only [Pi.zero_apply, integral_zero, zero_mul, mul_zero, zero_add]
    have hlog : 0 ≤ Real.log (2 * stableRank B) := by
      exact Real.log_nonneg (by linarith [one_le_stableRank hB])
    let k₀ : n := Classical.choice inferInstance
    have hsup : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (colNormSq B) :=
      (colNormSq_nonneg B k₀).trans
        (Finset.le_sup' (colNormSq B) (Finset.mem_univ k₀))
    exact mul_nonneg hlog hsup
  · exact intdim_column_submatrix_upper_of_isBernoulli B hB hq
      (lt_of_le_of_ne hq.1 (Ne.symm hq0')) hmeas hlaw hind

end IntrinsicColumnBernoulli

section IntrinsicUncentered

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [Nonempty m] [Nonempty n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {S : ι → Ω → Matrix m n ℂ} {L : ℝ}
variable {V₁ : Matrix m m ℂ} {V₂ : Matrix n n ℂ}

set_option maxHeartbeats 4000000 in
/-- **Book §7.3.1 discussion**: the uncentered intrinsic Bernstein tail with
the source's almost-sure centered norm bound.  This is the a.e. sibling of
`intdim_bernstein_uncentered_tail`. -/
theorem intdim_bernstein_uncentered_tail_ae
    (hmeas : ∀ k, Measurable (S k))
    (hbd : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω - expectation μ (S k)‖ ≤ L) (hL : 0 ≤ L)
    (hind : iIndepFun S μ)
    (hV₁psd : V₁.PosSemidef) (hV₂psd : V₂.PosSemidef)
    (hV0 : ¬(V₁ = 0 ∧ V₂ = 0))
    (hV₁ : (∑ k, expectation μ (fun ω => (S k ω - expectation μ (S k)) *
      (S k ω - expectation μ (S k))ᴴ)) ≤ V₁)
    (hV₂ : (∑ k, expectation μ (fun ω => (S k ω - expectation μ (S k))ᴴ *
      (S k ω - expectation μ (S k)))) ≤ V₂)
    {t : ℝ} (ht : Real.sqrt (max ‖V₁‖ ‖V₂‖) + L / 3 ≤ t) :
    μ.real {ω | t ≤ ‖(∑ k, S k ω) - ∑ k, expectation μ (S k)‖} ≤
      4 * intdim (Matrix.fromBlocks V₁ 0 0 V₂) *
        Real.exp (-(t ^ 2) / 2 / (max ‖V₁‖ ‖V₂‖ + L * t / 3)) := by
  classical
  let S' : ι → Ω → Matrix m n ℂ := fun k ω => S k ω - expectation μ (S k)
  have hmeas' : ∀ k, Measurable (S' k) := fun k =>
    (measurable_sub_const (expectation μ (S k))).comp (hmeas k)
  have hSint : ∀ k, MIntegrable (S k) μ := fun k => by
    refine MIntegrable.of_bound (hmeas k) (L + ‖expectation μ (S k)‖) ?_
    filter_upwards [hbd k] with ω hω
    intro i j
    calc ‖S k ω i j‖ ≤ ‖S k ω‖ := norm_entry_le_l2_opNorm_rect _ _ _
      _ ≤ ‖S k ω - expectation μ (S k)‖ + ‖expectation μ (S k)‖ := by
          nth_rewrite 1 [← sub_add_cancel (S k ω) (expectation μ (S k))]
          exact norm_add_le _ _
      _ ≤ L + ‖expectation μ (S k)‖ := add_le_add hω (le_refl _)
  have hcent' : ∀ k, expectation μ (S' k) = 0 := by
    intro k
    have hsub := expectation_sub (μ := μ) (hSint k)
      (MIntegrable.const (expectation μ (S k)))
    rw [show S' k = fun ω => S k ω - (fun _ : Ω => expectation μ (S k)) ω
      from rfl, hsub, expectation_const (μ := μ), sub_self]
  have hind' : iIndepFun S' μ :=
    hind.comp (fun k M => M - expectation μ (S k)) fun _ => measurable_sub_const _
  have h := intdim_bernstein_rect_tail_ae (μ := μ) hmeas' hbd hL hcent'
    hind' hV₁psd hV₂psd hV0 hV₁ hV₂ ht
  have hsum : ∀ ω, (∑ k, S' k ω) =
      (∑ k, S k ω) - ∑ k, expectation μ (S k) := fun ω => by
    change (∑ k, (S k ω - expectation μ (S k))) = _
    rw [Finset.sum_sub_distrib]
  rwa [show {ω | t ≤ ‖∑ k, S' k ω‖} =
      {ω | t ≤ ‖(∑ k, S k ω) - ∑ k, expectation μ (S k)‖} from by
        ext ω
        simp only [Set.mem_setOf_eq]
        rw [hsum ω]] at h

set_option maxHeartbeats 4000000 in
/-- **Book Corollary 7.3.2**, uncentered form mentioned in §7.3.1.  This is
the missing expectation companion to `intdim_bernstein_uncentered_tail`; it
uses the source-faithful almost-sure centered norm bound. -/
theorem intdim_bernstein_uncentered_expectation
    (hmeas : ∀ k, Measurable (S k))
    (hbd : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω - expectation μ (S k)‖ ≤ L) (hL : 0 ≤ L)
    (hind : iIndepFun S μ)
    (hV₁psd : V₁.PosSemidef) (hV₂psd : V₂.PosSemidef)
    (hV0 : ¬(V₁ = 0 ∧ V₂ = 0))
    (hV₁ : (∑ k, expectation μ (fun ω => (S k ω - expectation μ (S k)) *
      (S k ω - expectation μ (S k))ᴴ)) ≤ V₁)
    (hV₂ : (∑ k, expectation μ (fun ω => (S k ω - expectation μ (S k))ᴴ *
      (S k ω - expectation μ (S k)))) ≤ V₂) :
    ∫ ω, ‖(∑ k, S k ω) - ∑ k, expectation μ (S k)‖ ∂μ ≤
      10 * (Real.sqrt (max ‖V₁‖ ‖V₂‖ *
          Real.log (1 + intdim (Matrix.fromBlocks V₁ 0 0 V₂))) +
        L * Real.log (1 + intdim (Matrix.fromBlocks V₁ 0 0 V₂))) := by
  classical
  let S' : ι → Ω → Matrix m n ℂ := fun k ω => S k ω - expectation μ (S k)
  have hmeas' : ∀ k, Measurable (S' k) := fun k =>
    (measurable_sub_const (expectation μ (S k))).comp (hmeas k)
  have hSint : ∀ k, MIntegrable (S k) μ := fun k => by
    refine MIntegrable.of_bound (hmeas k) (L + ‖expectation μ (S k)‖) ?_
    filter_upwards [hbd k] with ω hω
    intro i j
    calc ‖S k ω i j‖ ≤ ‖S k ω‖ := norm_entry_le_l2_opNorm_rect _ _ _
      _ ≤ ‖S k ω - expectation μ (S k)‖ + ‖expectation μ (S k)‖ := by
          nth_rewrite 1 [← sub_add_cancel (S k ω) (expectation μ (S k))]
          exact norm_add_le _ _
      _ ≤ L + ‖expectation μ (S k)‖ := add_le_add hω (le_refl _)
  have hcent' : ∀ k, expectation μ (S' k) = 0 := by
    intro k
    have hsub := expectation_sub (μ := μ) (hSint k)
      (MIntegrable.const (expectation μ (S k)))
    rw [show S' k = fun ω => S k ω - (fun _ : Ω => expectation μ (S k)) ω
      from rfl, hsub, expectation_const (μ := μ), sub_self]
  have hind' : iIndepFun S' μ :=
    hind.comp (fun k M => M - expectation μ (S k)) fun _ => measurable_sub_const _
  have h := intdim_bernstein_rect_expectation (μ := μ) hmeas' hbd hL hcent'
    hind' hV₁psd hV₂psd hV0 hV₁ hV₂
  have hsum : ∀ ω, (∑ k, S' k ω) =
      (∑ k, S k ω) - ∑ k, expectation μ (S k) := fun ω => by
    change (∑ k, (S k ω - expectation μ (S k))) = _
    rw [Finset.sum_sub_distrib]
  rwa [show (fun ω => ‖∑ k, S' k ω‖) =
      fun ω => ‖(∑ k, S k ω) - ∑ k, expectation μ (S k)‖ from by
        funext ω
        rw [hsum ω]] at h

end IntrinsicUncentered

section IntrinsicSamplingAe

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [Nonempty m] [Nonempty n] [IsProbabilityMeasure μ]
variable {nn : ℕ} {R : Fin nn → Ω → Matrix m n ℂ} {R₀ : Ω → Matrix m n ℂ}
variable {B : Matrix m n ℂ} {L : ℝ} {M₁ : Matrix m m ℂ} {M₂ : Matrix n n ℂ}

/-- Lean implementation helper: an almost-sure matrix-norm bound over a
probability space has a nonnegative bound parameter. -/
private lemma intrinsicSampling_nonneg_of_ae_norm_le
    (hR₀m : Measurable R₀) (hbd : ∀ᵐ ω ∂μ, ‖R₀ ω‖ ≤ L) : 0 ≤ L := by
  have hnormm : Measurable fun ω => ‖R₀ ω‖ :=
    continuous_l2_opNorm.measurable.comp hR₀m
  have hnormint : Integrable (fun ω => ‖R₀ ω‖) μ := by
    refine Integrable.of_bound hnormm.aestronglyMeasurable |L| ?_
    filter_upwards [hbd] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hω.trans (le_abs_self L)
  have hmono : (∫ ω, ‖R₀ ω‖ ∂μ) ≤ ∫ _ : Ω, L ∂μ :=
    integral_mono_ae hnormint (integrable_const L) hbd
  rw [integral_const, probReal_univ, one_smul] at hmono
  exact (integral_nonneg fun _ => norm_nonneg _).trans hmono

/-- **Book Corollary 7.3.3, tail bound** with the template bound interpreted
almost surely.  This is the source-faithful sibling of
`matrix_sampling_intdim_tail`. -/
theorem matrix_sampling_intdim_tail_ae (hnn : 0 < nn)
    (hR₀m : Measurable R₀) (hbd : ∀ᵐ ω ∂μ, ‖R₀ ω‖ ≤ L)
    (hmean : expectation μ R₀ = B)
    (hM₁psd : M₁.PosSemidef) (hM₂psd : M₂.PosSemidef)
    (hM0 : ¬(M₁ = 0 ∧ M₂ = 0))
    (hM₁ : expectation μ (fun ω => R₀ ω * (R₀ ω)ᴴ) ≤ M₁)
    (hM₂ : expectation μ (fun ω => (R₀ ω)ᴴ * R₀ ω) ≤ M₂)
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, IdentDistrib (R k) R₀ μ μ) (hind : iIndepFun R μ)
    {t : ℝ} (ht : Real.sqrt (max ‖M₁‖ ‖M₂‖) + L / 3 ≤ t) :
    μ.real {ω | t ≤ ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖} ≤
      4 * intdim (Matrix.fromBlocks M₁ 0 0 M₂) *
        Real.exp (-(nn * t ^ 2) / 2 /
          (max ‖M₁‖ ‖M₂‖ + 2 * L * t / 3)) := by
  let R₀' : Ω → Matrix m n ℂ := fun ω => truncateNorm L (R₀ ω)
  have hL : 0 ≤ L := intrinsicSampling_nonneg_of_ae_norm_le hR₀m hbd
  have hae : R₀' =ᵐ[μ] R₀ := hbd.mono fun ω hω => by
    simp only [R₀', truncateNorm, if_pos hω]
  have hR₀m' : Measurable R₀' := measurable_truncateNorm.comp hR₀m
  have hbd' : ∀ ω, ‖R₀' ω‖ ≤ L := fun ω => truncateNorm_norm_le hL _
  have hmean' : expectation μ R₀' = B := by
    rw [expectation_congr_ae hae, hmean]
  have hM₁' : expectation μ (fun ω => R₀' ω * (R₀' ω)ᴴ) ≤ M₁ := by
    rw [expectation_congr_ae (hae.mono fun ω hω => by rw [hω])]
    exact hM₁
  have hM₂' : expectation μ (fun ω => (R₀' ω)ᴴ * R₀' ω) ≤ M₂ := by
    rw [expectation_congr_ae (hae.mono fun ω hω => by rw [hω])]
    exact hM₂
  have hid' : ∀ k, IdentDistrib (R k) R₀' μ μ := fun k =>
    (hid k).trans (IdentDistrib.of_ae_eq hR₀m.aemeasurable hae.symm)
  exact matrix_sampling_intdim_tail (μ := μ) hnn hR₀m' hbd' hmean'
    hM₁psd hM₂psd hM0 hM₁' hM₂' hmeas hid' hind ht

/-- **Book Corollary 7.3.3, expectation bound** with the template bound
interpreted almost surely.  This is the source-faithful sibling of
`matrix_sampling_intdim_expectation`. -/
theorem matrix_sampling_intdim_expectation_ae (hnn : 0 < nn)
    (hR₀m : Measurable R₀) (hbd : ∀ᵐ ω ∂μ, ‖R₀ ω‖ ≤ L)
    (hmean : expectation μ R₀ = B)
    (hM₁psd : M₁.PosSemidef) (hM₂psd : M₂.PosSemidef)
    (hM0 : ¬(M₁ = 0 ∧ M₂ = 0))
    (hM₁ : expectation μ (fun ω => R₀ ω * (R₀ ω)ᴴ) ≤ M₁)
    (hM₂ : expectation μ (fun ω => (R₀ ω)ᴴ * R₀ ω) ≤ M₂)
    (hmeas : ∀ k, Measurable (R k))
    (hid : ∀ k, IdentDistrib (R k) R₀ μ μ) (hind : iIndepFun R μ) :
    ∫ ω, ‖(nn : ℝ)⁻¹ • (∑ k, R k ω) - B‖ ∂μ ≤
      10 * Real.sqrt (max ‖M₁‖ ‖M₂‖ *
          Real.log (1 + intdim (Matrix.fromBlocks M₁ 0 0 M₂)) / nn) +
        20 * L * Real.log (1 + intdim (Matrix.fromBlocks M₁ 0 0 M₂)) / nn := by
  let R₀' : Ω → Matrix m n ℂ := fun ω => truncateNorm L (R₀ ω)
  have hL : 0 ≤ L := intrinsicSampling_nonneg_of_ae_norm_le hR₀m hbd
  have hae : R₀' =ᵐ[μ] R₀ := hbd.mono fun ω hω => by
    simp only [R₀', truncateNorm, if_pos hω]
  have hR₀m' : Measurable R₀' := measurable_truncateNorm.comp hR₀m
  have hbd' : ∀ ω, ‖R₀' ω‖ ≤ L := fun ω => truncateNorm_norm_le hL _
  have hmean' : expectation μ R₀' = B := by
    rw [expectation_congr_ae hae, hmean]
  have hM₁' : expectation μ (fun ω => R₀' ω * (R₀' ω)ᴴ) ≤ M₁ := by
    rw [expectation_congr_ae (hae.mono fun ω hω => by rw [hω])]
    exact hM₁
  have hM₂' : expectation μ (fun ω => (R₀' ω)ᴴ * R₀' ω) ≤ M₂ := by
    rw [expectation_congr_ae (hae.mono fun ω hω => by rw [hω])]
    exact hM₂
  have hid' : ∀ k, IdentDistrib (R k) R₀' μ μ := fun k =>
    (hid k).trans (IdentDistrib.of_ae_eq hR₀m.aemeasurable hae.symm)
  exact matrix_sampling_intdim_expectation (μ := μ) hnn hR₀m' hbd' hmean'
    hM₁psd hM₂psd hM0 hM₁' hM₂' hmeas hid' hind

end IntrinsicSamplingAe

end MatrixConcentration

set_option linter.unusedSectionVars false

/-!
# One-sided intrinsic matrix Bernstein counterparts

The declarations in this section retain the intrinsic-dimension constants of
Book Theorem 7.7.1 while interpreting the upper spectral-edge hypothesis almost
everywhere.  Explicit first- and second-moment integrability replaces the
earlier auxiliary two-sided norm bound.
-/

namespace MatrixConcentration

open Matrix MeasureTheory Finset ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {X : ι → Ω → Matrix n n ℂ} {L : ℝ} {V : Matrix n n ℂ}

section OneSidedIntrinsicBernstein

/-- Lean implementation helper: a finite Hermitian sum is controlled by
pointwise upper edges supplied for the matrices at one fixed sample. -/
private lemma lambdaMax_sum_le_sum_of_forall (s : Finset ι)
    {A : ι → Matrix n n ℂ} (hA : ∀ k, (A k).IsHermitian)
    {U : ι → ℝ} (hmax : ∀ k, lambdaMax (hA k) ≤ U k) :
    lambdaMax (isHermitian_matsum s hA) ≤ ∑ k ∈ s, U k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lambdaMax_zero_matrix]
  | @insert a s ha ih =>
      have hadd := lambdaMax_add_le (hA a)
        (isHermitian_matsum s hA)
      have hsum : (∑ k ∈ insert a s, A k) = A a + ∑ k ∈ s, A k := by
        rw [Finset.sum_insert ha]
      rw [lambdaMax_congr hsum
        (isHermitian_matsum (insert a s) hA)
        ((hA a).add (isHermitian_matsum s hA)), Finset.sum_insert ha]
      exact hadd.trans (add_le_add (hmax a) ih)

/-- Lean implementation helper: a positive matrix exponential has integrable
real trace under an almost-everywhere upper spectral-edge bound. -/
lemma integrable_trace_exp_re_of_lambdaMax_bound_ae
    {Y : Ω → Matrix n n ℂ} (hYm : Measurable Y)
    (hYherm : ∀ ω, (Y ω).IsHermitian) {U θ : ℝ}
    (hmax : ∀ᵐ ω ∂μ, lambdaMax (hYherm ω) ≤ U) (hθ : 0 < θ) :
    Integrable (fun ω => ((NormedSpace.exp (θ • Y ω)).trace).re) μ := by
  have hExpint : MIntegrable (fun ω => NormedSpace.exp (θ • Y ω)) μ := by
    refine MIntegrable.of_bound
      (measurable_matrixExp_comp (hYm.const_smul θ))
      (Real.exp (θ * U)) ?_
    filter_upwards [hmax] with ω hω
    intro i j
    calc
      ‖NormedSpace.exp (θ • Y ω) i j‖ ≤ ‖NormedSpace.exp (θ • Y ω)‖ :=
        norm_entry_le_l2_opNorm _ _ _
      _ = Real.exp (lambdaMax (isHermitian_real_smul (hYherm ω) θ)) := by
        rw [posSemidef_l2_opNorm_eq_lambdaMax
          (posDef_exp (isHermitian_real_smul (hYherm ω) θ)).posSemidef,
          lambdaMax_exp]
      _ = Real.exp (θ * lambdaMax (hYherm ω)) := by
        rw [lambdaMax_smul_nonneg (hYherm ω) hθ.le]
      _ ≤ Real.exp (θ * U) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hω hθ.le)
  have hdiag : ∀ i, Integrable
      (fun ω => (NormedSpace.exp (θ • Y ω) i i).re) μ :=
    fun i => (hExpint i i).re
  simpa [Matrix.trace] using
    (integrable_finsetSum Finset.univ fun i _ => hdiag i)

/-- Lean implementation helper: entrywise first-moment integrability implies
integrability of the real trace. -/
lemma integrable_trace_re_of_mintegrable {Y : Ω → Matrix n n ℂ}
    (hYint : MIntegrable Y μ) : Integrable (fun ω => ((Y ω).trace).re) μ := by
  have hdiag : ∀ i, Integrable (fun ω => (Y ω i i).re) μ :=
    fun i => (hYint i i).re
  simpa [Matrix.trace] using
    (integrable_finsetSum Finset.univ fun i _ => hdiag i)

/-- Lean implementation helper: the centered trace cancellation with explicit
entrywise first-moment integrability. -/
lemma integral_trace_re_eq_zero_of_mintegrable
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hcent : ∀ k, expectation μ (X k) = 0) :
    ∫ ω, ((∑ k, X k ω).trace).re ∂μ = 0 := by
  have h1 : (fun ω => ((∑ k, X k ω).trace).re) =
      fun ω => ∑ k, (((X k ω).trace).re) := by
    funext ω
    rw [Matrix.trace_sum, Complex.re_sum]
  rw [h1, MeasureTheory.integral_finsetSum (μ := μ) Finset.univ
    (f := fun k (ω : Ω) => (((X k ω).trace).re)) fun k _ =>
      integrable_trace_re_of_mintegrable (hXint k)]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h2 : (fun ω => (((X k ω).trace).re)) =
      fun ω => ∑ i, ((X k ω) i i).re := by
    funext ω
    rw [Matrix.trace, Complex.re_sum]
    rfl
  rw [h2, MeasureTheory.integral_finsetSum (μ := μ) Finset.univ
    (f := fun i (ω : Ω) => ((X k ω) i i).re) fun i _ => (hXint k i i).re]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h3 : ∫ ω, (X k ω i i).re ∂μ = (∫ ω, X k ω i i ∂μ).re :=
    integral_re (hXint k i i)
  rw [h3, show (∫ ω, X k ω i i ∂μ) = expectation μ (X k) i i from
    (expectation_apply _ _ _).symm, hcent k]
  simp

/-- Lean implementation helper: pointwise-edge form of the intrinsic
Bernstein trace-mgf comparison. -/
private lemma bernstein_trace_mgf_bound_one_sided_pointwise
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L)
    (hindep : iIndepFun X μ) {θ : ℝ} (hθ : 0 < θ)
    (hθL : θ * L < 3) :
    ∫ ω, ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re ∂μ ≤
      ((NormedSpace.exp (gBernstein θ L •
        ∑ k, expectation μ (fun ω => X k ω * X k ω))).trace).re := by
  have h1 := trace_exp_sum_le_trace_exp_sum_cgf_one_sided
    (μ := μ) hmeas hherm hmax hindep hθ
  have hrw : (fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re) =
      fun ω => ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re := by
    funext ω
    rw [Finset.smul_sum]
  rw [hrw]
  refine h1.trans ?_
  have hcgf_le : ∀ k, matrixCgf μ (X k) θ ≤
      gBernstein θ L • expectation μ (fun ω => X k ω * X k ω) :=
    fun k => bernstein_matrix_cgf_le_one_sided (μ := μ) (hmeas k)
      (hherm k) (hXint k) (hX2int k) (hcent k) (hmax k) hθ hθL
  have hsum_le : (∑ k, matrixCgf μ (X k) θ) ≤
      gBernstein θ L • ∑ k, expectation μ (fun ω => X k ω * X k ω) := by
    rw [Finset.smul_sum]
    exact sum_loewner_mono Finset.univ fun k _ => hcgf_le k
  have hcgfHerm : (∑ k, matrixCgf μ (X k) θ).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => isHermitian_cfc_log _
  have hE2herm : ∀ k,
      (expectation μ (fun ω => X k ω * X k ω)).IsHermitian := fun k =>
    isHermitian_expectation
      (Filter.Eventually.of_forall fun ω => isHermitian_sq (hherm k ω))
  have hEsumHerm :
      (∑ k, expectation μ (fun ω => X k ω * X k ω)).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => hE2herm k
  exact trace_exp_monotone hcgfHerm (isHermitian_real_smul hEsumHerm _)
    hsum_le

/-- **Book §7.7.1, second proof display**, under an almost-sure one-sided
upper spectral edge and explicit first/second-moment integrability.  This is
the source-faithful counterpart of `bernstein_trace_mgf_bound`. -/
theorem bernstein_trace_mgf_bound_one_sided
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hindep : iIndepFun X μ) {θ : ℝ} (hθ : 0 < θ)
    (hθL : θ * L < 3) :
    ∫ ω, ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re ∂μ ≤
      ((NormedSpace.exp (gBernstein θ L •
        ∑ k, expectation μ (fun ω => X k ω * X k ω))).trace).re := by
  classical
  let X' : ι → Ω → Matrix n n ℂ := fun k =>
    truncateLambdaMax L (X k) (hherm k)
  have hae : ∀ k, X' k =ᵐ[μ] X k := fun k =>
    truncateLambdaMax_ae_eq (hherm k) (hmax k)
  have hmeas' : ∀ k, Measurable (X' k) := fun k =>
    measurable_truncateLambdaMax (hmeas k) (hherm k)
  have hherm' : ∀ k ω, (X' k ω).IsHermitian := fun k =>
    isHermitian_truncateLambdaMax (hherm k)
  have hmax' : ∀ k ω, lambdaMax (hherm' k ω) ≤ L := fun k =>
    lambdaMax_truncateLambdaMax_le (hherm k) hL
  have hXint' : ∀ k, MIntegrable (X' k) μ := fun k =>
    (hXint k).congr_ae (hae k).symm
  have hX2int' : ∀ k, MIntegrable (fun ω => X' k ω * X' k ω) μ := fun k =>
    (hX2int k).congr_ae ((hae k).symm.mono fun ω hω =>
      congrArg (fun A : Matrix n n ℂ => A * A) hω)
  have hcent' : ∀ k, expectation μ (X' k) = 0 := fun k => by
    rw [expectation_congr_ae (hae k), hcent k]
  have hindep' : iIndepFun X' μ :=
    iIndepFun.congr (fun k => (hae k).symm) hindep
  have h := bernstein_trace_mgf_bound_one_sided_pointwise (μ := μ)
    hmeas' hherm' hXint' hX2int' hcent' hmax' hindep' hθ hθL
  have hall : ∀ᵐ ω ∂μ, ∀ k, X' k ω = X k ω :=
    (MeasureTheory.ae_all_iff).mpr hae
  have hsum : (fun ω => ∑ k, X' k ω) =ᵐ[μ]
      fun ω => ∑ k, X k ω :=
    hall.mono fun ω hω => Finset.sum_congr rfl fun k _ => hω k
  have hlhs : (fun ω =>
      ((NormedSpace.exp (θ • ∑ k, X' k ω)).trace).re) =ᵐ[μ]
      fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re :=
    hsum.mono fun ω hω => congrArg
      (fun A : Matrix n n ℂ => ((NormedSpace.exp (θ • A)).trace).re) hω
  have hsquare : ∀ k, (fun ω => X' k ω * X' k ω) =ᵐ[μ]
      fun ω => X k ω * X k ω := fun k =>
    (hae k).mono fun ω hω => congrArg (fun A : Matrix n n ℂ => A * A) hω
  rw [integral_congr_ae hlhs,
    Finset.sum_congr rfl fun k _ => expectation_congr_ae (hsquare k)] at h
  exact h

/-- **Book §7.7.1, display (7.7.2)** with the source's almost-sure one-sided
spectral hypothesis and explicit first/second-moment integrability.  This is
the source-faithful counterpart of `bernstein_expected_trace_bound`. -/
theorem bernstein_expected_trace_bound_one_sided
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hindep : iIndepFun X μ) (hVpsd : V.PosSemidef)
    (hV : (∑ k, expectation μ (fun ω => X k ω * X k ω)) ≤ V)
    {θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) :
    ∫ ω, (((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
        (Fintype.card n : ℝ)) ∂μ ≤
      intdim V * Real.exp (gBernstein θ L * ‖V‖) := by
  have hgpos : 0 < gBernstein θ L := by
    rw [gBernstein]
    exact div_pos (by positivity) (by linarith)
  have hYmeas : Measurable fun ω => ∑ k, X k ω :=
    measurable_matsum Finset.univ hmeas
  have hYherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hmaxAll : ∀ᵐ ω ∂μ, ∀ k, lambdaMax (hherm k ω) ≤ L :=
    (MeasureTheory.ae_all_iff).mpr hmax
  have hYmax : ∀ᵐ ω ∂μ,
      lambdaMax (hYherm ω) ≤ ∑ _k : ι, L :=
    hmaxAll.mono fun ω hω => by
      simpa using
        (lambdaMax_sum_le_sum_of_forall (Finset.univ : Finset ι)
          (fun k => hherm k ω) (fun k => hω k))
  have hint : Integrable
      (fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re) μ :=
    integrable_trace_exp_re_of_lambdaMax_bound_ae hYmeas hYherm hYmax hθ
  rw [integral_sub hint (integrable_const _), integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have h1 := bernstein_trace_mgf_bound_one_sided (μ := μ) hmeas hherm
    hXint hX2int hcent hmax hL hindep hθ hθL
  have hE2herm : ∀ k,
      (expectation μ (fun ω => X k ω * X k ω)).IsHermitian := fun k =>
    isHermitian_expectation
      (Filter.Eventually.of_forall fun ω => isHermitian_sq (hherm k ω))
  have hEsumHerm :
      (∑ k, expectation μ (fun ω => X k ω * X k ω)).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => hE2herm k
  have hgE : (gBernstein θ L •
      ∑ k, expectation μ (fun ω => X k ω * X k ω)) ≤
      gBernstein θ L • V := by
    rw [Matrix.le_iff, ← smul_sub]
    exact posSemidef_smul_nonneg (Matrix.le_iff.mp hV) hgpos.le
  have h2 := trace_exp_monotone (isHermitian_real_smul hEsumHerm _)
    (isHermitian_real_smul hVpsd.1 _) hgE
  have hgVpsd : (gBernstein θ L • V).PosSemidef :=
    posSemidef_smul_nonneg hVpsd hgpos.le
  have h3 := trace_exp_sub_card_le_intdim_exp hgVpsd
  have h4 : intdim (gBernstein θ L • V) = intdim V :=
    intdim_smul hgpos V
  have h5 : ‖gBernstein θ L • V‖ = gBernstein θ L * ‖V‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hgpos]
  rw [h4, h5] at h3
  linarith [h1, h2, h3]

/-- **Book §7.7.1, display (7.7.1)**: the `ψ₂` Laplace step under an
almost-sure upper spectral edge.  This is the one-sided/a.e. counterpart of
`intdim_laplace_psiTwo`: explicit entrywise integrability supplies the linear
trace term, while the one-sided edge supplies exponential integrability. -/
theorem intdim_laplace_psiTwo_one_sided
    {Y : Ω → Matrix n n ℂ} (hYm : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) (hYint : MIntegrable Y μ)
    {U : ℝ} (hmax : ∀ᵐ ω ∂μ, lambdaMax (hHerm ω) ≤ U)
    {t θ : ℝ} (ht : 0 < t) (hθ : 0 < θ) :
    μ.real {ω | t ≤ lambdaMax (hHerm ω)} ≤
      (Real.exp (θ * t) - θ * t - 1)⁻¹ *
        ∫ ω, (((NormedSpace.exp (θ • Y ω)).trace).re -
          θ * ((Y ω).trace).re - (Fintype.card n : ℝ)) ∂μ := by
  have hWherm : ∀ ω, (θ • Y ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hHerm ω) θ
  have hpoint : ∀ ω, ∑ i, psiTwo 1 ((hWherm ω).eigenvalues i) =
      ((NormedSpace.exp (θ • Y ω)).trace).re - θ * ((Y ω).trace).re -
        (Fintype.card n : ℝ) := by
    intro ω
    have h1 : ∀ i, psiTwo 1 ((hWherm ω).eigenvalues i) =
        Real.exp ((hWherm ω).eigenvalues i) - (hWherm ω).eigenvalues i - 1 :=
      fun i => by rw [psiTwo, one_mul]
    have htrW : ∑ i, (hWherm ω).eigenvalues i =
        θ * ((Y ω).trace).re := by
      rw [← trace_re_eq_sum_eigenvalues (hWherm ω), Matrix.trace_smul,
        Complex.smul_re, smul_eq_mul]
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    rw [show (fun i => Real.exp ((hWherm ω).eigenvalues i) -
        (hWherm ω).eigenvalues i - 1) = fun i =>
        (Real.exp ((hWherm ω).eigenvalues i) - (hWherm ω).eigenvalues i) - 1
      from rfl, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, htrW,
      trace_exp_re_eq_sum (hWherm ω)]
  have hevent : {ω | t ≤ lambdaMax (hHerm ω)} =
      {ω | θ * t ≤ lambdaMax (hWherm ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [lambdaMax_smul_nonneg (hHerm ω) hθ.le (hWherm ω)]
    exact ⟨fun h => mul_le_mul_of_nonneg_left h hθ.le,
      fun h => le_of_mul_le_mul_left h hθ⟩
  have hψt : 0 < psiTwo 1 (θ * t) := by
    rw [psiTwo, one_mul]
    have h1 := Real.add_one_lt_exp (ne_of_gt (mul_pos hθ ht))
    linarith
  have hint : Integrable
      (fun ω => ∑ i, psiTwo 1 ((hWherm ω).eigenvalues i)) μ := by
    rw [show (fun ω => ∑ i, psiTwo 1 ((hWherm ω).eigenvalues i)) =
        fun ω => ((NormedSpace.exp (θ • Y ω)).trace).re -
          θ * ((Y ω).trace).re - (Fintype.card n : ℝ)
      from funext hpoint]
    exact ((integrable_trace_exp_re_of_lambdaMax_bound_ae
      hYm hHerm hmax hθ).sub
        ((integrable_trace_re_of_mintegrable hYint).const_mul θ)).sub
          (integrable_const _)
  have h := generalized_matrix_laplace_tail (μ := μ)
    (fun s => psiTwo_nonneg 1 s) (by
      have := psiTwo_monotoneOn (θ := 1) zero_le_one
      exact this)
    hWherm (mul_nonneg hθ.le ht.le) hψt hint
  rw [hevent]
  refine h.trans ?_
  rw [psiTwo, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by
    have h1 := Real.add_one_le_exp (θ * t)
    linarith))
  refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall ?_))
  exact hpoint

/-- **Book Theorem 7.7.1, core form**, under an almost-sure one-sided upper
spectral edge and explicit first/second-moment integrability.  This is the
source-faithful counterpart of `intdim_bernstein_herm_tail_core`: for `t > 0`
and `t² ≥ ‖V‖ + Lt/3`, the same intrinsic-dimension constant is obtained
without a two-sided norm bound. -/
theorem intdim_bernstein_herm_tail_core_one_sided
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hindep : iIndepFun X μ) (hVpsd : V.PosSemidef) (hV0 : V ≠ 0)
    (hV : (∑ k, expectation μ (fun ω => X k ω * X k ω)) ≤ V)
    {t : ℝ} (ht : 0 < t) (htv : ‖V‖ + L * t / 3 ≤ t ^ 2) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        fun k => hherm k ω)} ≤
      4 * intdim V * Real.exp (-(t ^ 2) / 2 / (‖V‖ + L * t / 3)) := by
  classical
  set v : ℝ := ‖V‖ with hvdef
  have hvpos : 0 < v := norm_pos_iff.mpr hV0
  set D : ℝ := v + L * t / 3 with hDdef
  have hDpos : 0 < D := by
    have h1 : 0 ≤ L * t / 3 := by positivity
    simp only [hDdef]
    linarith
  set θ : ℝ := t / D with hθdef
  have hθpos : 0 < θ := div_pos ht hDpos
  have hθL : θ * L < 3 := by
    rw [hθdef, div_mul_eq_mul_div, div_lt_iff₀ hDpos]
    simp only [hDdef]
    nlinarith [hvpos, ht]
  have hYmeas : Measurable fun ω => ∑ k, X k ω :=
    measurable_matsum Finset.univ hmeas
  have hYherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYint : MIntegrable (fun ω => ∑ k, X k ω) μ :=
    MIntegrable.finsetSum (μ := μ) Finset.univ fun k _ => hXint k
  have hmaxAll : ∀ᵐ ω ∂μ, ∀ k, lambdaMax (hherm k ω) ≤ L :=
    (MeasureTheory.ae_all_iff).mpr hmax
  have hYmax : ∀ᵐ ω ∂μ,
      lambdaMax (hYherm ω) ≤ ∑ _k : ι, L :=
    hmaxAll.mono fun ω hω => by
      simpa using
        (lambdaMax_sum_le_sum_of_forall (Finset.univ : Finset ι)
          (fun k => hherm k ω) (fun k => hω k))
  have h1 := intdim_laplace_psiTwo_one_sided (μ := μ)
    (Y := fun ω => ∑ k, X k ω) hYmeas hYherm hYint hYmax ht hθpos
  have hinttr : Integrable
      (fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re) μ :=
    integrable_trace_exp_re_of_lambdaMax_bound_ae
      hYmeas hYherm hYmax hθpos
  have hinttrY : Integrable (fun ω => ((∑ k, X k ω).trace).re) μ :=
    integrable_trace_re_of_mintegrable hYint
  have hEtrY : ∫ ω, ((∑ k, X k ω).trace).re ∂μ = 0 :=
    integral_trace_re_eq_zero_of_mintegrable hXint hcent
  have hsplit : ∫ ω,
      (((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
        θ * ((∑ k, X k ω).trace).re - (Fintype.card n : ℝ)) ∂μ =
      ∫ ω, (((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
        (Fintype.card n : ℝ)) ∂μ := by
    have hfun : (fun ω =>
        ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
          θ * ((∑ k, X k ω).trace).re - (Fintype.card n : ℝ)) =
        fun ω => (((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
          (Fintype.card n : ℝ)) - θ * ((∑ k, X k ω).trace).re := by
      funext ω
      ring
    have hsub1 : Integrable (fun ω =>
        ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re -
          (Fintype.card n : ℝ)) μ := hinttr.sub (integrable_const _)
    have hsub2 : Integrable
        (fun ω => θ * ((∑ k, X k ω).trace).re) μ := hinttrY.const_mul θ
    rw [hfun, integral_sub hsub1 hsub2, integral_const_mul, hEtrY,
      mul_zero, sub_zero]
  have h2 := bernstein_expected_trace_bound_one_sided (μ := μ)
    hmeas hherm hXint hX2int hcent hmax hL hindep hVpsd hV hθpos hθL
  have hψpos : 0 < Real.exp (θ * t) - θ * t - 1 := by
    have := Real.add_one_lt_exp (ne_of_gt (mul_pos hθpos ht))
    linarith
  have h3 : μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
      fun k => hherm k ω)} ≤
      (Real.exp (θ * t) - θ * t - 1)⁻¹ *
        (intdim V * Real.exp (gBernstein θ L * v)) := by
    refine h1.trans ?_
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hψpos.le)
  have hθt : θ * t = t ^ 2 / D := by
    rw [hθdef, div_mul_eq_mul_div, sq]
  have hθt1 : 1 ≤ θ * t := by
    rw [hθt, le_div_iff₀ hDpos, one_mul]
    simpa only [hDdef, hvdef] using htv
  have hfrac : (Real.exp (θ * t) - θ * t - 1)⁻¹ ≤
      4 * Real.exp (-(θ * t)) := by
    have h8 := exp_div_psiTwo_le (mul_pos hθpos ht)
    have h9 : 1 + 3 / (θ * t) ^ 2 ≤ 4 := by
      have h10 : 3 / (θ * t) ^ 2 ≤ 3 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hθt1]
      linarith
    have h11 : (Real.exp (θ * t) - θ * t - 1)⁻¹ =
        Real.exp (-(θ * t)) *
          (Real.exp (θ * t) / (Real.exp (θ * t) - θ * t - 1)) := by
      rw [Real.exp_neg]
      field_simp
    rw [h11]
    calc Real.exp (-(θ * t)) *
        (Real.exp (θ * t) / (Real.exp (θ * t) - θ * t - 1))
        ≤ Real.exp (-(θ * t)) * 4 :=
          mul_le_mul_of_nonneg_left (h8.trans h9) (Real.exp_pos _).le
      _ = 4 * Real.exp (-(θ * t)) := by ring
  have hexpid : gBernstein θ L * v + -(θ * t) = -(t ^ 2) / 2 / D := by
    have h1mθL : 1 - θ * L / 3 = v / D := by
      rw [hθdef]
      field_simp
      simp only [hDdef]
      ring
    rw [gBernstein, h1mθL, hθdef]
    have hvne : v ≠ 0 := ne_of_gt hvpos
    field_simp
    ring
  refine h3.trans ?_
  have hd0 : 0 ≤ intdim V := intdim_nonneg hVpsd
  calc (Real.exp (θ * t) - θ * t - 1)⁻¹ *
      (intdim V * Real.exp (gBernstein θ L * v))
      ≤ 4 * Real.exp (-(θ * t)) *
        (intdim V * Real.exp (gBernstein θ L * v)) :=
        mul_le_mul_of_nonneg_right hfrac
          (mul_nonneg hd0 (Real.exp_pos _).le)
    _ = 4 * intdim V *
        (Real.exp (gBernstein θ L * v) * Real.exp (-(θ * t))) := by ring
    _ = 4 * intdim V * Real.exp (-(t ^ 2) / 2 / D) := by
      rw [← Real.exp_add, hexpid]

/-- **Book Theorem 7.7.1 (Matrix Bernstein: Hermitian Case with Intrinsic
Dimension)** under its literal one-sided spectral-edge hypothesis, interpreted
almost everywhere.  Explicit first/second-moment integrability replaces the
two-sided norm bound in `intdim_bernstein_herm_tail`, with the same constant. -/
theorem intdim_bernstein_herm_tail_one_sided
    (hmeas : ∀ k, Measurable (X k))
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hXint : ∀ k, MIntegrable (X k) μ)
    (hX2int : ∀ k, MIntegrable (fun ω => X k ω * X k ω) μ)
    (hcent : ∀ k, expectation μ (X k) = 0)
    (hmax : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hindep : iIndepFun X μ) (hVpsd : V.PosSemidef) (hV0 : V ≠ 0)
    (hV : (∑ k, expectation μ (fun ω => X k ω * X k ω)) ≤ V)
    {t : ℝ} (ht : Real.sqrt ‖V‖ + L / 3 ≤ t) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        fun k => hherm k ω)} ≤
      4 * intdim V * Real.exp (-(t ^ 2) / 2 / (‖V‖ + L * t / 3)) := by
  have hvpos : 0 < ‖V‖ := norm_pos_iff.mpr hV0
  have htpos : 0 < t := by
    have h1 : 0 < Real.sqrt ‖V‖ := Real.sqrt_pos.mpr hvpos
    have h2 : 0 ≤ L / 3 := by positivity
    linarith
  exact intdim_bernstein_herm_tail_core_one_sided hmeas hherm hXint hX2int
    hcent hmax hL hindep hVpsd hV0 hV htpos
    (bernstein_threshold_sq (norm_nonneg V) hL ht)

end OneSidedIntrinsicBernstein

end MatrixConcentration
