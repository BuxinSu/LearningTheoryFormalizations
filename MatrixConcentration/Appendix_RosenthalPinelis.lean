import MatrixConcentration.Appendix_MatrixRosenthal
import MatrixConcentration.Chapter4_MatrixGaussianAndRademacherSeries
import MatrixConcentration.Chapter5_SumOfPSDMatrices
import MatrixConcentration.Chapter8_ProofOfLiebsTheorem
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Appendix: Matrix Rosenthal–Pinelis inequalities

This module supplies the two proved variants associated with **Book equation (6.1.6)**.

This appendix contains:

* Schatten-norm and sharp noncommutative Khintchine infrastructure;
* a verified rectangular Rosenthal–Pinelis reduction;
* symmetric rectangular estimates;
* the centered estimate with its explicit symmetrization loss.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Appendix: Schatten and Rosenthal--Pinelis infrastructure

Book display **(6.1.6)** gives a centered rectangular Rosenthal--Pinelis
estimate with the coefficients `sqrt (2 * e * log D)` and `4 * e * log D`.
The cited source [CGT12a, Theorem A.1(2)] obtains those constants under
distributional symmetry. This module therefore supports two proved variants:

* an exact-constant theorem for independent, distributionally symmetric
  summands;
* a centered theorem obtained by independent-copy symmetrization, with
  coefficient losses `sqrt 2` and `2`.

The literal centered/exact Book display **(6.1.6)** is not asserted as a Lean
theorem. The declarations below provide the Schatten functional, explicit
Khintchine/bootstrap predicates and reductions, Rademacher second moments,
ghost-copy identities, and the complete proofs of the two stated variants.
-/
namespace MatrixConcentration

open Matrix MeasureTheory ProbabilityTheory Finset Function
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

section DilationMeasurability

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Lean implementation helper: measurability of the Hermitian dilation as a
map on matrices. -/
lemma measurable_hermDilation_fun :
    Measurable fun B : Matrix m n ℂ => hermDilation B := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  rcases i with i | i <;> rcases j with j | j
  · show Measurable fun _ : Matrix m n ℂ => (0 : ℂ)
    exact measurable_const
  · show Measurable fun B : Matrix m n ℂ => B i j
    exact measurable_entry i j
  · show Measurable fun B : Matrix m n ℂ => star (B j i)
    exact continuous_star.measurable.comp (measurable_entry j i)
  · show Measurable fun _ : Matrix m n ℂ => (0 : ℂ)
    exact measurable_const

end DilationMeasurability

section RectangularIntegrability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable [IsProbabilityMeasure μ]

/-- Lean implementation helper: rectangular version of the entry bound
`|a_{ij}| ≤ ‖A‖`. -/
lemma norm_entry_le_l2_opNorm_rect {p q : Type*} [Fintype p] [Fintype q]
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
  have hsingle1 : l2norm (Pi.single i (1 : ℂ) : p → ℂ) = 1 := l2norm_single i
  have hsingle2 : l2norm (Pi.single j (1 : ℂ) : q → ℂ) = 1 := l2norm_single j
  rw [h1, hsingle1, hsingle2] at h
  simpa using h

/-- Lean implementation helper: entrywise integrability of a rectangular
random matrix from a norm bound. -/
lemma mintegrable_rect_of_norm_bound {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] {Z : Ω → Matrix p q ℂ} {C : ℝ}
    (hZm : Measurable Z) (hbd : ∀ ω, ‖Z ω‖ ≤ C) : MIntegrable Z μ := by
  refine MIntegrable.of_bound hZm C
    (Filter.Eventually.of_forall fun ω i j => ?_)
  exact (norm_entry_le_l2_opNorm_rect _ _ _).trans (hbd ω)

end RectangularIntegrability

noncomputable section

universe uI uN uΩ

section SchattenFunctional

variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- Lean implementation helper.

The numerical real-exponent Schatten functional
`(Σᵢ σᵢ(B)^r)^(1/r)`.  It is deliberately not bundled as a `Norm`:
only the numerical functional and the comparison lemmas needed below are used. -/
noncomputable def schattenR (r : ℝ) (B : Matrix m n ℂ) : ℝ :=
  (∑ i, (singularValues B i) ^ r) ^ r⁻¹

/-- Lean implementation helper. -/
lemma schattenR_nonneg (r : ℝ) (B : Matrix m n ℂ) : 0 ≤ schattenR r B := by
  exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (singularValues_nonneg B i) r) r⁻¹

/-- Lean implementation helper.

Each singular value is dominated by the positive-exponent Schatten
functional. -/
lemma singularValue_le_schattenR {r : ℝ} (hr : 0 < r)
    (B : Matrix m n ℂ) (i : n) : singularValues B i ≤ schattenR r B := by
  rw [schattenR, Real.le_rpow_inv_iff_of_pos
    (singularValues_nonneg B i)
    (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (singularValues_nonneg B j) r) hr]
  exact Finset.single_le_sum
    (fun j _ => Real.rpow_nonneg (singularValues_nonneg B j) r)
    (Finset.mem_univ i)

/-- Lean implementation helper.

The operator norm is the Schatten-infinity endpoint, hence is bounded by
each positive finite Schatten functional. -/
lemma l2_opNorm_le_schattenR [Nonempty n] {r : ℝ} (hr : 0 < r)
    (B : Matrix m n ℂ) : ‖B‖ ≤ schattenR r B := by
  rw [l2_opNorm_eq_sup_singularValues]
  exact ciSup_le fun i => singularValue_le_schattenR hr B i

/-- Lean implementation helper. -/
lemma singularValue_le_l2_opNorm [Nonempty n] (B : Matrix m n ℂ) (i : n) :
    singularValues B i ≤ ‖B‖ := by
  rw [l2_opNorm_eq_sup_singularValues]
  exact le_ciSup (Set.Finite.bddAbove (Set.finite_range (singularValues B))) i

/-- Lean implementation helper.

The dimension version of the finite Schatten/operator comparison. -/
lemma schattenR_le_card_mul_l2_opNorm [Nonempty n] {r : ℝ} (hr : 0 < r)
    (B : Matrix m n ℂ) :
    schattenR r B ≤ (Fintype.card n : ℝ) ^ r⁻¹ * ‖B‖ := by
  have hsum : (∑ i, (singularValues B i) ^ r) ≤
      (Fintype.card n : ℝ) * ‖B‖ ^ r := by
    calc
      (∑ i, (singularValues B i) ^ r) ≤ ∑ _i : n, ‖B‖ ^ r := by
        exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow
          (singularValues_nonneg B i) (singularValue_le_l2_opNorm B i) hr.le
      _ = (Fintype.card n : ℝ) * ‖B‖ ^ r := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [schattenR]
  calc
    (∑ i, (singularValues B i) ^ r) ^ r⁻¹ ≤
        ((Fintype.card n : ℝ) * ‖B‖ ^ r) ^ r⁻¹ := by
      exact Real.rpow_le_rpow
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg B i) r)
        hsum (inv_nonneg.mpr hr.le)
    _ = (Fintype.card n : ℝ) ^ r⁻¹ * ‖B‖ := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg B) r),
        Real.rpow_rpow_inv (norm_nonneg B) hr.ne']

/-- Lean implementation helper.

The sharper rank version of the finite Schatten/operator comparison. -/
lemma schattenR_le_rank_mul_l2_opNorm [Nonempty n] {r : ℝ} (hr : 0 < r)
    (B : Matrix m n ℂ) :
    schattenR r B ≤ (B.rank : ℝ) ^ r⁻¹ * ‖B‖ := by
  let hH : (Bᴴ * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self B
  have hcard :
      (Finset.univ.filter (fun i => (singularValues B i) ^ r ≠ 0)).card = B.rank := by
    have hfilt :
        Finset.univ.filter (fun i => (singularValues B i) ^ r ≠ 0) =
          Finset.univ.filter (fun i => hH.eigenvalues i ≠ 0) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Real.rpow_ne_zero (singularValues_nonneg B i) hr.ne']
      rw [← sq_singularValues B i]
      exact not_congr (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).symm
    rw [hfilt, ← Matrix.rank_conjTranspose_mul_self B,
      hH.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hfilter :
      ∑ i ∈ Finset.univ.filter (fun i => (singularValues B i) ^ r ≠ 0),
          (singularValues B i) ^ r = ∑ i, (singularValues B i) ^ r :=
    Finset.sum_filter_ne_zero _
  have hsum : (∑ i, (singularValues B i) ^ r) ≤
      (B.rank : ℝ) * ‖B‖ ^ r := by
    rw [← hfilter]
    have hbound : ∀ i ∈ Finset.univ.filter (fun i => (singularValues B i) ^ r ≠ 0),
        (singularValues B i) ^ r ≤ ‖B‖ ^ r := fun i _ =>
      Real.rpow_le_rpow (singularValues_nonneg B i)
        (singularValue_le_l2_opNorm B i) hr.le
    have h := Finset.sum_le_card_nsmul _ _ _ hbound
    rw [hcard, nsmul_eq_mul] at h
    exact h
  rw [schattenR]
  calc
    (∑ i, (singularValues B i) ^ r) ^ r⁻¹ ≤
        ((B.rank : ℝ) * ‖B‖ ^ r) ^ r⁻¹ := by
      exact Real.rpow_le_rpow
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg B i) r)
        hsum (inv_nonneg.mpr hr.le)
    _ = (B.rank : ℝ) ^ r⁻¹ * ‖B‖ := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg B) r),
        Real.rpow_rpow_inv (norm_nonneg B) hr.ne']

/-- Lean implementation helper. -/
lemma singularValues_zero [Nonempty n] (i : n) :
    singularValues (0 : Matrix m n ℂ) i = 0 := by
  exact le_antisymm (by simpa using
    (singularValue_le_l2_opNorm (0 : Matrix m n ℂ) i))
    (singularValues_nonneg (0 : Matrix m n ℂ) i)

/-- Lean implementation helper. -/
lemma schattenR_eq_zero_iff [Nonempty n] {r : ℝ} (hr : 0 < r)
    (B : Matrix m n ℂ) : schattenR r B = 0 ↔ B = 0 := by
  constructor
  · intro h
    exact norm_eq_zero.mp (le_antisymm ((l2_opNorm_le_schattenR hr B).trans_eq h)
      (norm_nonneg B))
  · rintro rfl
    simp [schattenR, singularValues_zero, Real.zero_rpow hr.ne', hr.ne']

/-- Lean implementation helper.

The new functional extends the project's existing Schatten one-functional. -/
lemma schattenR_one_eq_schattenOneNorm (B : Matrix m n ℂ) :
    schattenR 1 B = schattenOneNorm B := by
  simp [schattenR, schattenOneNorm]

/-- Lean implementation helper.

The exponent-two Schatten functional is the Frobenius norm. -/
lemma schattenR_two_eq_frobeniusNorm (B : Matrix m n ℂ) :
    schattenR 2 B = frobeniusNorm B := by
  rw [schattenR]
  simp_rw [Real.rpow_two]
  rw [← frobenius_norm_sq_eq_sum_singularValues_sq,
    show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (frobeniusNorm_nonneg B)]

/-- Lean implementation helper.

The exact dimension factor used at `r = 2 log D`. -/
lemma natCast_rpow_one_div_two_log_eq_sqrt_exp (D : ℕ) (hD : 1 < D) :
    (D : ℝ) ^ (1 / (2 * Real.log (D : ℝ))) = Real.sqrt (Real.exp 1) := by
  have hD0 : 0 < (D : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hD)
  have hD1 : (D : ℝ) ≠ 1 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hlog : Real.log (D : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hD0 hD1
  calc
    (D : ℝ) ^ (1 / (2 * Real.log (D : ℝ))) =
        (D : ℝ) ^ ((Real.log (D : ℝ))⁻¹ * (1 / 2 : ℝ)) := by
      congr 1
      field_simp
    _ = ((D : ℝ) ^ (Real.log (D : ℝ))⁻¹) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_mul hD0.le]
    _ = (Real.exp 1) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_inv_log hD0 hD1]
    _ = Real.sqrt (Real.exp 1) := (Real.sqrt_eq_rpow _).symm

/-- Lean implementation helper: the second elementary real-power/logarithm identity. -/
lemma natCast_rpow_two_div_two_log_eq_exp (D : ℕ) (hD : 1 < D) :
    (D : ℝ) ^ (2 / (2 * Real.log (D : ℝ))) = Real.exp 1 := by
  have hD0 : 0 < (D : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hD)
  have hD1 : (D : ℝ) ≠ 1 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hlog : Real.log (D : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hD0 hD1
  rw [show 2 / (2 * Real.log (D : ℝ)) =
    (Real.log (D : ℝ))⁻¹ by field_simp]
  exact Real.rpow_inv_log hD0 hD1

/-- Lean implementation helper: the public comparison does not require a nonempty column
type.  In the empty-column case every matrix is zero and the defining sum is
empty. -/
lemma l2_opNorm_le_schattenR_general {r : ℝ} (hr : 0 < r)
    (B : Matrix m n ℂ) : ‖B‖ ≤ schattenR r B := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hB : B = 0 := by ext i j; exact isEmptyElim j
    subst B
    simp [schattenR, Real.zero_rpow (inv_ne_zero hr.ne')]
  · exact l2_opNorm_le_schattenR hr B

/-- Lean implementation helper. -/
lemma schattenR_le_card_mul_l2_opNorm_general {r : ℝ} (hr : 0 < r)
    (B : Matrix m n ℂ) :
    schattenR r B ≤ (Fintype.card n : ℝ) ^ r⁻¹ * ‖B‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hB : B = 0 := by ext i j; exact isEmptyElim j
    subst B
    simp [schattenR, Real.zero_rpow (inv_ne_zero hr.ne')]
  · exact schattenR_le_card_mul_l2_opNorm hr B

/-- Lean implementation helper. -/
lemma schattenR_le_rank_mul_l2_opNorm_general {r : ℝ} (hr : 0 < r)
    (B : Matrix m n ℂ) :
    schattenR r B ≤ (B.rank : ℝ) ^ r⁻¹ * ‖B‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hB : B = 0 := by ext i j; exact isEmptyElim j
    subst B
    simp [schattenR, Real.zero_rpow (inv_ne_zero hr.ne')]
  · exact schattenR_le_rank_mul_l2_opNorm hr B

/-- Lean implementation helper. -/
lemma schattenR_eq_zero_iff_general {r : ℝ} (hr : 0 < r)
    (B : Matrix m n ℂ) : schattenR r B = 0 ↔ B = 0 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hB : B = 0 := by ext i j; exact isEmptyElim j
    subst B
    simp [schattenR, Real.zero_rpow (inv_ne_zero hr.ne')]
  · exact schattenR_eq_zero_iff hr B

end SchattenFunctional

section KhintchineStatements

/-! **Conditional-only infrastructure.**  The predicates and reductions in
this section do not provide a proof of noncommutative Khintchine with the sharp
constant.  No witness for either predicate is asserted in this development;
all unconditional Rosenthal--Pinelis results below are proved separately. -/

/-- Lean implementation helper.

The precise Hermitian noncommutative Khintchine moment statement at one
real exponent and one constant, packaged as a proposition that can be passed
explicitly to reduction theorems. -/
def HermitianNCKhintchineAt (r κ : ℝ) : Prop :=
  ∀ {I : Type uI} {n : Type uN} [Fintype I] [DecidableEq I]
    [Fintype n] [DecidableEq n] [Nonempty n]
    (A : I → Matrix n n ℂ) (_hA : ∀ k, (A k).IsHermitian),
    (∫ b : I → Bool, schattenR r (signSum b A) ^ r
        ∂Measure.pi fun _ : I => boolRademacherMeasure) ^ r⁻¹ ≤
      κ * schattenR r (posSqrt (∑ k, (A k) ^ 2))

/-- Lean implementation helper.

The rectangular operator-norm consequence expected from Hermitian
Khintchine after dilation and Schatten/operator comparison.  It is separated
from `HermitianNCKhintchineAt` because deriving it also needs moment
monotonicity and the square-root/Schatten identities. -/
def RectangularNCKhintchineAt (r κ : ℝ) : Prop :=
  ∀ {I : Type uI} [Fintype I] [DecidableEq I] {p q : ℕ}
    (A : I → Matrix (Fin p) (Fin q) ℂ),
    (∫ b : I → Bool,
        ‖∑ k, boolSign (b k) • A k‖ ^ r
          ∂Measure.pi fun _ : I => boolRademacherMeasure) ^ r⁻¹ ≤
      κ * ((p + q : ℕ) : ℝ) ^ r⁻¹ *
        Real.sqrt
          (max ‖∑ k, A k * (A k)ᴴ‖ ‖∑ k, (A k)ᴴ * A k‖)

/-- Lean implementation helper.

The operator norm of the positive matrix square root. -/
lemma l2_opNorm_posSqrt {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    ‖posSqrt M‖ = Real.sqrt ‖M‖ := by
  have hsquare := l2_opNorm_sq_mul_conjTranspose_self (posSqrt M)
  rw [isHermitian_posSqrt M, posSqrt_mul_self hM] at hsquare
  symm
  rw [hsquare, Real.sqrt_sq (norm_nonneg (posSqrt M))]

/-- Lean implementation helper.

Hermitian Schatten-moment NC Khintchine implies its rectangular
operator-moment consequence by Hermitian dilation.  This proof also supplies
the exact dimension factor used later. -/
theorem hermitian_nckhintchine_implies_rectangular
    {r κ : ℝ} (hr : 0 < r) (hκ : 0 ≤ κ)
    (hherm : HermitianNCKhintchineAt.{uI, 0} r κ) :
    RectangularNCKhintchineAt.{uI} r κ := by
  intro I _ _ p q A
  by_cases hD : p + q = 0
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    have hA : A = fun _ => 0 := by
      funext k
      ext i
      exact Fin.elim0 i
    subst A
    simp [Real.zero_rpow hr.ne', Real.zero_rpow (inv_ne_zero hr.ne')]
  · letI : Nonempty (Fin p ⊕ Fin q) :=
      Fintype.card_pos_iff.mp (by
        rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
        omega)
    let H : I → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
      fun k => hermDilation (A k)
    have hH : ∀ k, (H k).IsHermitian := fun k => isHermitian_hermDilation (A k)
    have hsign : ∀ b : I → Bool,
        signSum b H = hermDilation (∑ k, boolSign (b k) • A k) := by
      intro b
      symm
      simpa [H, signSum] using
        (hermDilation_sum_smul (Finset.univ : Finset I)
          (fun k => boolSign (b k)) A)
    have hsquare : ∀ k, ((H k) ^ 2).PosSemidef := by
      intro k
      simpa [pow_two] using posSemidef_sq (hH k)
    have hsumsq : (∑ k, (H k) ^ 2).PosSemidef :=
      posSemidef_matsum Finset.univ hsquare
    have hint :
        (∫ b : I → Bool,
            ‖∑ k, boolSign (b k) • A k‖ ^ r
              ∂Measure.pi fun _ : I => boolRademacherMeasure) ≤
          ∫ b : I → Bool, schattenR r (signSum b H) ^ r
              ∂Measure.pi fun _ : I => boolRademacherMeasure := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro b
      apply Real.rpow_le_rpow (norm_nonneg _) _ hr.le
      rw [← l2_opNorm_hermDilation, ← hsign b]
      exact l2_opNorm_le_schattenR hr (signSum b H)
    have hleft0 : 0 ≤
        ∫ b : I → Bool,
            ‖∑ k, boolSign (b k) • A k‖ ^ r
              ∂Measure.pi fun _ : I => boolRademacherMeasure := by
      apply integral_nonneg
      intro b
      exact Real.rpow_nonneg (norm_nonneg _) r
    have houter :
        (∫ b : I → Bool,
            ‖∑ k, boolSign (b k) • A k‖ ^ r
              ∂Measure.pi fun _ : I => boolRademacherMeasure) ^ r⁻¹ ≤
          (∫ b : I → Bool, schattenR r (signSum b H) ^ r
              ∂Measure.pi fun _ : I => boolRademacherMeasure) ^ r⁻¹ :=
      Real.rpow_le_rpow hleft0 hint (inv_nonneg.mpr hr.le)
    have hkh := hherm (I := I) H hH
    have hrhs :
        schattenR r (posSqrt (∑ k, (H k) ^ 2)) ≤
          (((p + q : ℕ) : ℝ) ^ r⁻¹) *
            Real.sqrt
              (max ‖∑ k, A k * (A k)ᴴ‖ ‖∑ k, (A k)ᴴ * A k‖) := by
      calc
        schattenR r (posSqrt (∑ k, (H k) ^ 2)) ≤
            (Fintype.card (Fin p ⊕ Fin q) : ℝ) ^ r⁻¹ *
              ‖posSqrt (∑ k, (H k) ^ 2)‖ :=
          schattenR_le_card_mul_l2_opNorm hr _
        _ = (((p + q : ℕ) : ℝ) ^ r⁻¹) *
            Real.sqrt
              (max ‖∑ k, A k * (A k)ᴴ‖ ‖∑ k, (A k)ᴴ * A k‖) := by
          rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
            l2_opNorm_posSqrt hsumsq]
          congr 2
          exact dilation_coeff_sq_norm A
    refine houter.trans (hkh.trans ?_)
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hrhs hκ

/-- Lean implementation helper.

The analytic bridge from deterministic rectangular Khintchine estimates to
general centered summands, packaged with the exact ghost-symmetrization
coefficients needed by the reduction below. -/
def ProvidesCenteredRosenthalBootstrap (r κ : ℝ) : Prop :=
  RectangularNCKhintchineAt.{uI} r κ →
  ∀ {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {I : Type uI} [Fintype I] [DecidableEq I]
    {p q : ℕ} {S : I → Ω → Matrix (Fin p) (Fin q) ℂ},
    iIndepFun S μ →
    (∀ k, Measurable (S k)) →
    (∀ k, expectation μ (S k) = 0) →
    (∃ R : I → ℝ, ∀ k ω, ‖S k ω‖ ≤ R k) →
    (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ≤
      Real.sqrt 2 *
          (κ * ((p + q : ℕ) : ℝ) ^ r⁻¹) *
          Real.sqrt
            (max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
              ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖) +
        4 * (κ * ((p + q : ℕ) : ℝ) ^ r⁻¹) ^ 2 *
          Real.sqrt (maxSummandSq S μ)

end KhintchineStatements

section ExactConstantAssembly

/-- Lean implementation helper.

The scalar coefficient calculation used to reach the coefficients in Book
display (6.1.6). Both terms are controlled by `K² ≤ e * ℓ`. -/
lemma rosenthal_pinelis_constant_algebra
    {V M K ℓ : ℝ} (hV : 0 ≤ V) (hK : 0 ≤ K) (hℓ : 0 ≤ ℓ)
    (hKsq : K ^ 2 ≤ Real.exp 1 * ℓ) :
    Real.sqrt 2 * K * Real.sqrt V + 4 * K ^ 2 * Real.sqrt M ≤
      Real.sqrt (2 * Real.exp 1 * V * ℓ) +
        4 * Real.exp 1 * Real.sqrt M * ℓ := by
  have hfirst_nonneg : 0 ≤ Real.sqrt 2 * K * Real.sqrt V :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hK) (Real.sqrt_nonneg V)
  have hrad_nonneg : 0 ≤ 2 * Real.exp 1 * V * ℓ := by positivity
  have hfirst_sq :
      (Real.sqrt 2 * K * Real.sqrt V) ^ 2 ≤
        (Real.sqrt (2 * Real.exp 1 * V * ℓ)) ^ 2 := by
    rw [Real.sq_sqrt hrad_nonneg]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt hV]
    nlinarith [hKsq]
  have hfirst : Real.sqrt 2 * K * Real.sqrt V ≤
      Real.sqrt (2 * Real.exp 1 * V * ℓ) := by
    nlinarith [hfirst_nonneg, Real.sqrt_nonneg (2 * Real.exp 1 * V * ℓ)]
  have hsecond : 4 * K ^ 2 * Real.sqrt M ≤
      4 * Real.exp 1 * Real.sqrt M * ℓ := by
    nlinarith [Real.sqrt_nonneg M]
  exact add_le_add hfirst hsecond

/-- Lean implementation helper.

At `r = 2 log D`, the sharp real-exponent bound `κ² ≤ r/2`
is exactly sufficient for the centered coefficient condition. -/
lemma sharp_khintchine_constant_is_sufficient {D : ℕ} (hD : 1 < D)
    {r κ : ℝ} (hr : r = 2 * Real.log D) (hκ : κ ^ 2 ≤ r / 2) :
    (κ * (D : ℝ) ^ r⁻¹) ^ 2 ≤ Real.exp 1 * Real.log D := by
  have hfac : (((D : ℝ) ^ r⁻¹) : ℝ) ^ 2 = Real.exp 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2)
      (natCast_rpow_one_div_two_log_eq_sqrt_exp D hD)
    rw [Real.sq_sqrt (Real.exp_pos 1).le] at h
    simpa [hr, one_div] using h
  rw [mul_pow, hfac]
  rw [hr] at hκ
  have hκ' : κ ^ 2 ≤ Real.log D := by
    nlinarith [hκ]
  have hm := mul_le_mul_of_nonneg_right hκ' (Real.exp_pos 1).le
  nlinarith

section ConditionalReduction

variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure μ]
variable {d₁ d₂ : ℕ} {I : Type uI} [Fintype I] [DecidableEq I]

/-- Lean implementation helper.

A reduction to the literal centered/exact conclusion of Book display (6.1.6)
under explicit rectangular Khintchine and centered-bootstrap premises. -/
theorem matrix_rosenthal_pinelis_of_nck_and_bootstrap
    {S : I → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (h_indep : iIndepFun S μ)
    (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, expectation μ (S k) = 0)
    {R : I → ℝ} (h_bdd : ∀ k ω, ‖S k ω‖ ≤ R k)
    {r κ : ℝ}
    (h_nck : RectangularNCKhintchineAt.{uI} r κ)
    (h_bootstrap : ProvidesCenteredRosenthalBootstrap.{uI, uΩ} r κ)
    (hκ : 0 ≤ κ)
    (hconstant :
      (κ * ((d₁ + d₂ : ℕ) : ℝ) ^ r⁻¹) ^ 2 ≤
        Real.exp 1 * Real.log (d₁ + d₂)) :
    (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ≤
      Real.sqrt (2 * Real.exp 1 *
        (max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖) *
        Real.log (d₁ + d₂)) +
      4 * Real.exp 1 * (maxSummandSq S μ) ^ ((1 : ℝ) / 2) *
        Real.log (d₁ + d₂) := by
  let K : ℝ := κ * ((d₁ + d₂ : ℕ) : ℝ) ^ r⁻¹
  let V : ℝ :=
    max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
      ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖
  let M : ℝ := maxSummandSq S μ
  have hK0 : 0 ≤ K :=
    mul_nonneg hκ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hV0 : 0 ≤ V :=
    (norm_nonneg _).trans (le_max_left _ _)
  have hℓ0 : 0 ≤ Real.log (d₁ + d₂) := by
    have hE : 0 ≤ Real.exp 1 * Real.log (d₁ + d₂) :=
      (sq_nonneg K).trans (by simpa [K] using hconstant)
    have hE' : 0 ≤ Real.log (d₁ + d₂) * Real.exp 1 := by
      simpa [mul_comm] using hE
    exact nonneg_of_mul_nonneg_left hE' (Real.exp_pos 1)
  have hpre := h_bootstrap h_nck (S := S) h_indep h_meas h_cent ⟨R, h_bdd⟩
  have h := rosenthal_pinelis_constant_algebra
    (V := V) (M := M) (K := K) (ℓ := Real.log (d₁ + d₂))
    hV0 hK0 hℓ0 (by simpa [K] using hconstant)
  have hpre' :
      (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ≤
        Real.sqrt 2 * K * Real.sqrt V + 4 * K ^ 2 * Real.sqrt M := by
    simpa [K, V, M] using hpre
  exact hpre'.trans (by simpa [V, M, Real.sqrt_eq_rpow] using h)

/-- Lean implementation helper.

The `r = 2 log D` specialization of the preceding reduction, retaining the
rectangular Khintchine and centered-bootstrap premises explicitly. -/
theorem matrix_rosenthal_pinelis_of_sharp_nck_and_bootstrap
    {S : I → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (h_indep : iIndepFun S μ)
    (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, expectation μ (S k) = 0)
    {R : I → ℝ} (h_bdd : ∀ k ω, ‖S k ω‖ ≤ R k)
    (hD : 1 < d₁ + d₂) {κ : ℝ}
    (h_nck : RectangularNCKhintchineAt.{uI}
      (2 * Real.log (d₁ + d₂)) κ)
    (h_bootstrap : ProvidesCenteredRosenthalBootstrap.{uI, uΩ}
      (2 * Real.log (d₁ + d₂)) κ)
    (hκ0 : 0 ≤ κ)
    (hκsharp : κ ^ 2 ≤ (2 * Real.log (d₁ + d₂)) / 2) :
    (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ≤
      Real.sqrt (2 * Real.exp 1 *
        (max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖) *
        Real.log (d₁ + d₂)) +
      4 * Real.exp 1 * (maxSummandSq S μ) ^ ((1 : ℝ) / 2) *
        Real.log (d₁ + d₂) := by
  apply matrix_rosenthal_pinelis_of_nck_and_bootstrap
    h_indep h_meas h_cent h_bdd h_nck h_bootstrap hκ0
  have hκsharp' : κ ^ 2 ≤
      (2 * Real.log (((d₁ + d₂ : ℕ) : ℝ))) / 2 := by
    simpa [Nat.cast_add] using hκsharp
  simpa [Nat.cast_add] using
    (sharp_khintchine_constant_is_sufficient hD rfl hκsharp')

end ConditionalReduction

end ExactConstantAssembly

end

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Symmetric exact constants and centered symmetrization losses

`matrix_rosenthal_pinelis_symmetric_aux` proves the exact coefficients from
[CGT12a, Theorem A.1(2)] under distributional symmetry.
`matrix_rosenthal_pinelis_centered_with_loss_aux` assumes only centering and
uses an independent copy, producing the respective `sqrt 2` and `2` losses.
The Chapter 6 module exposes these results under their public names.
-/
namespace MatrixConcentration

open Matrix MeasureTheory ProbabilityTheory Finset Function
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

noncomputable section

universe uI uΩ uOmega

section BoolRademacherSecondMoment

variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {p q : ℕ} [Nonempty (Fin p)] [Nonempty (Fin q)]

/-- Lean implementation helper.

The second-moment form of the rectangular Rademacher-series estimate,
specialized to the canonical finite Boolean product probability space. -/
theorem bool_rademacher_rect_expect_sq_upper
    (A : I → Matrix (Fin p) (Fin q) ℂ) :
    ∫ b : I → Bool, ‖∑ k, boolSign (b k) • A k‖ ^ 2
        ∂(Measure.pi fun _ : I => boolRademacherMeasure) ≤
      2 * max ‖∑ k, A k * (A k)ᴴ‖ ‖∑ k, (A k)ᴴ * A k‖ *
        (1 + Real.log (p + q)) := by
  classical
  let μb : Measure (I → Bool) := Measure.pi fun _ : I => boolRademacherMeasure
  let ϱ : I → (I → Bool) → ℝ := fun k b => boolSign (b k)
  let v : ℝ := max ‖∑ k, A k * (A k)ᴴ‖ ‖∑ k, (A k)ᴴ * A k‖
  let D : ℝ := p + q
  have hD1 : (1 : ℝ) ≤ D := by
    dsimp only [D]
    have hp1 : (1 : ℝ) ≤ p := by
      have hp0 : 0 < p := by
        simpa using Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin p))
      exact_mod_cast hp0
    have hq0 : (0 : ℝ) ≤ q := by positivity
    linarith
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hlogD : (0 : ℝ) ≤ Real.log D := Real.log_nonneg hD1
  have hvnn : 0 ≤ v := (norm_nonneg _).trans (le_max_left _ _)
  have hϱmeas : ∀ k, Measurable (ϱ k) := fun k =>
    measurable_boolSign.comp (measurable_pi_apply k)
  have hϱlaw : ∀ k, IsRademacher (ϱ k) μb := fun k => boolSign_law k
  have hϱrange : ∀ k b, ϱ k b = 1 ∨ ϱ k b = -1 := by
    intro k b
    cases hb : b k <;> simp [ϱ, boolSign, hb]
  have hϱind : iIndepFun ϱ μb := boolSign_indep
  rcases eq_or_lt_of_le hvnn with hv0 | hvpos
  · have hA0 : ∀ k, A k = 0 :=
      coeffs_eq_zero_of_variance_eq_zero (by simpa [v] using hv0.symm)
    have hint0 : (fun b : I → Bool => ‖∑ k, ϱ k b • A k‖ ^ 2) =
        fun _ => (0 : ℝ) := by
      funext b
      have hsum : (∑ k, ϱ k b • A k) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hA0 k, smul_zero]
      rw [hsum]
      simp
    change (∫ b, ‖∑ k, ϱ k b • A k‖ ^ 2 ∂μb) ≤ _
    rw [hint0, integral_zero]
    change 0 ≤ 2 * v * (1 + Real.log D)
    rw [← hv0]
    norm_num
  set E : ℝ := Real.sqrt (2 * v * Real.log D) with hEdef
  have hEnn : 0 ≤ E := Real.sqrt_nonneg _
  have hE2 : E ^ 2 = 2 * v * Real.log D := Real.sq_sqrt (by positivity)
  have hZmeas : Measurable fun b => ∑ k, ϱ k b • A k := by
    exact Finset.measurable_sum Finset.univ fun k _ =>
      (hϱmeas k).smul_const (A k)
  have hnormmeas : Measurable fun b => ‖∑ k, ϱ k b • A k‖ :=
    continuous_l2_opNorm.measurable.comp hZmeas
  have hlc := lintegral_comp_eq_lintegral_meas_le_mul μb
    (f := fun b => ‖∑ k, ϱ k b • A k‖) (g := fun t => 2 * t)
    (Filter.Eventually.of_forall fun b => norm_nonneg _)
    hnormmeas.aemeasurable
    (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      have : (0 : ℝ) < t := ht
      positivity)
  have hsqint : ∀ x : ℝ, (∫ t in (0 : ℝ)..x, 2 * t) = x ^ 2 := by
    intro x
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have hLHSlc :
      ∫⁻ b, ENNReal.ofReal (‖∑ k, ϱ k b • A k‖ ^ 2) ∂μb =
        ∫⁻ t in Set.Ioi (0 : ℝ),
          μb {b | t ≤ ‖∑ k, ϱ k b • A k‖} * ENNReal.ofReal (2 * t) := by
    rw [← hlc]
    refine lintegral_congr fun b => ?_
    rw [hsqint]
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
    have heq2 : -(2 * v * D * (Real.exp (-(t ^ 2) / (2 * v)) * -(t / v))) =
        D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t) := by
      field_simp
    rwa [heq2] at h4
  have hgpos : ∀ t ∈ Set.Ioi E,
      0 ≤ D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t) := by
    intro t ht
    have ht0 : 0 ≤ t := hEnn.trans (le_of_lt ht)
    positivity
  have hcont : ContinuousWithinAt
      (fun t => -(2 * v * D * Real.exp (-(t ^ 2) / (2 * v)))) (Set.Ici E) E := by
    refine Continuous.continuousWithinAt ?_
    fun_prop
  have htends : Filter.Tendsto
      (fun t => -(2 * v * D * Real.exp (-(t ^ 2) / (2 * v))))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => -(t ^ 2) / (2 * v)) Filter.atTop
        Filter.atBot := by
      apply Filter.Tendsto.atBot_div_const (by positivity)
      exact Filter.tendsto_neg_atBot_iff.mpr
        (Filter.tendsto_pow_atTop two_ne_zero)
    have h2 : Filter.Tendsto (fun t : ℝ => Real.exp (-(t ^ 2) / (2 * v)))
        Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp h1
    have h3 := (h2.const_mul (2 * v * D)).neg
    simpa using h3
  have hFTCint : IntegrableOn
      (fun t => D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t)) (Set.Ioi E) :=
    integrableOn_Ioi_deriv_of_nonneg hcont hderiv hgpos htends
  have hFTCval : ∫ t in Set.Ioi E,
      D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t) =
        2 * v * D * Real.exp (-(E ^ 2) / (2 * v)) := by
    rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hgpos htends]
    ring
  have hkey :
      ∫⁻ b, ENNReal.ofReal (‖∑ k, ϱ k b • A k‖ ^ 2) ∂μb ≤
        ENNReal.ofReal (E ^ 2) +
          ENNReal.ofReal (2 * v * D * Real.exp (-(E ^ 2) / (2 * v))) := by
    rw [hLHSlc]
    have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 E ∪ Set.Ioi E :=
      (Set.Ioc_union_Ioi_eq_Ioi hEnn).symm
    rw [hsplit, lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl)]
    refine add_le_add ?_ ?_
    · calc
        ∫⁻ t in Set.Ioc 0 E,
            μb {b | t ≤ ‖∑ k, ϱ k b • A k‖} * ENNReal.ofReal (2 * t)
            ≤ ∫⁻ t in Set.Ioc 0 E, 1 * ENNReal.ofReal (2 * t) :=
              lintegral_mono fun t => mul_le_mul_right' prob_le_one _
        _ = ∫⁻ t in Set.Ioc 0 E, ENNReal.ofReal (2 * t) := by simp
        _ = ENNReal.ofReal (∫ t in Set.Ioc 0 E, 2 * t) := by
          have h2tint : IntegrableOn (fun t : ℝ => 2 * t) (Set.Ioc 0 E) := by
            apply Continuous.integrableOn_Ioc
            fun_prop
          rw [← ofReal_integral_eq_lintegral_ofReal h2tint
            (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
              have : (0 : ℝ) < t := ht.1
              positivity)]
        _ = ENNReal.ofReal (E ^ 2) := by
          rw [← intervalIntegral.integral_of_le hEnn, hsqint]
    · calc
        ∫⁻ t in Set.Ioi E,
            μb {b | t ≤ ‖∑ k, ϱ k b • A k‖} * ENNReal.ofReal (2 * t)
            ≤ ∫⁻ t in Set.Ioi E,
              ENNReal.ofReal
                (D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t)) := by
          refine lintegral_mono_ae
            (ae_restrict_of_forall_mem measurableSet_Ioi fun t htE => ?_)
          have ht0 : 0 ≤ t := hEnn.trans (le_of_lt htE)
          have htail := rademacher_series_rect_tail
            (B := A) (μ := μb) hϱmeas hϱlaw hϱrange hϱind ht0
          have h1 : μb {b | t ≤ ‖∑ k, ϱ k b • A k‖} =
              ENNReal.ofReal (μb.real {b | t ≤ ‖∑ k, ϱ k b • A k‖}) :=
            (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
          rw [h1, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          exact mul_le_mul_of_nonneg_right (by simpa [v, D] using htail) (by positivity)
        _ = ENNReal.ofReal
            (∫ t in Set.Ioi E,
              D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t)) :=
          (ofReal_integral_eq_lintegral_ofReal hFTCint
            (ae_restrict_of_forall_mem measurableSet_Ioi hgpos)).symm
        _ = ENNReal.ofReal
            (2 * v * D * Real.exp (-(E ^ 2) / (2 * v))) := by rw [hFTCval]
  have hBochner :
      (∫ b, ‖∑ k, ϱ k b • A k‖ ^ 2 ∂μb) =
        (∫⁻ b, ENNReal.ofReal (‖∑ k, ϱ k b • A k‖ ^ 2) ∂μb).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun b => sq_nonneg _)
      ((hnormmeas.pow_const 2).aestronglyMeasurable)]
  have hne : ENNReal.ofReal (E ^ 2) +
      ENNReal.ofReal (2 * v * D * Real.exp (-(E ^ 2) / (2 * v))) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hexpE : Real.exp (-(E ^ 2) / (2 * v)) = D⁻¹ := by
    have hv2 : (2 * v) ≠ 0 := by positivity
    have harg : -(E ^ 2) / (2 * v) = -Real.log D := by
      rw [hE2, show 2 * v * Real.log D = Real.log D * (2 * v) by ring,
        neg_div, mul_div_cancel_right₀ _ hv2]
    rw [harg, Real.exp_neg, Real.exp_log hDpos]
  change (∫ b, ‖∑ k, ϱ k b • A k‖ ^ 2 ∂μb) ≤ _
  calc
    (∫ b, ‖∑ k, ϱ k b • A k‖ ^ 2 ∂μb) =
        (∫⁻ b, ENNReal.ofReal (‖∑ k, ϱ k b • A k‖ ^ 2) ∂μb).toReal :=
      hBochner
    _ ≤ (ENNReal.ofReal (E ^ 2) +
          ENNReal.ofReal (2 * v * D * Real.exp (-(E ^ 2) / (2 * v)))).toReal :=
      ENNReal.toReal_mono hne hkey
    _ = E ^ 2 + 2 * v * D * Real.exp (-(E ^ 2) / (2 * v)) := by
      rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (sq_nonneg _),
        ENNReal.toReal_ofReal (by positivity)]
    _ = 2 * v * Real.log D + 2 * v := by
      rw [hexpE, hE2, mul_assoc (2 * v) D D⁻¹,
        mul_inv_cancel₀ (ne_of_gt hDpos), mul_one]
    _ = 2 * v * (1 + Real.log D) := by ring
    _ = 2 * max ‖∑ k, A k * (A k)ᴴ‖ ‖∑ k, (A k)ᴴ * A k‖ *
        (1 + Real.log (p + q)) := by
      simp only [v, D]


end BoolRademacherSecondMoment

section SymmetricCentering

variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- Lean implementation helper.

A measurable distributionally symmetric random matrix is centered.  No
separate integrability premise is needed for this identity because Lean's
Bochner integral, and hence `expectation`, is defined to be zero outside the
integrable case. -/
lemma expectation_eq_zero_of_isSymmetricRV
    {X : Ω → Matrix m n ℂ} (hX : Measurable X)
    (hsymm : IsSymmetricRV X μ) : expectation μ X = 0 := by
  ext i j
  have hentry : Measurable (fun A : Matrix m n ℂ => A i j) :=
    measurable_entry i j
  have hneg : Measurable (fun ω => -(X ω)) := hX.neg
  have heq : (∫ ω, X ω i j ∂μ) = -(∫ ω, X ω i j ∂μ) := by
    calc
      (∫ ω, X ω i j ∂μ) =
          ∫ A, A i j ∂(μ.map X) := by
            symm
            exact integral_map hX.aemeasurable hentry.aestronglyMeasurable
      _ = ∫ A, A i j ∂(μ.map fun ω => -(X ω)) := by rw [hsymm]
      _ = ∫ ω, (-(X ω)) i j ∂μ :=
        integral_map hneg.aemeasurable hentry.aestronglyMeasurable
      _ = -(∫ ω, X ω i j ∂μ) := by
        simp only [Matrix.neg_apply, integral_neg]
  simpa only [expectation_apply, Matrix.zero_apply] using
    (CharZero.eq_neg_self_iff.mp heq)

end SymmetricCentering

section TraceBound

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Lean implementation helper. -/
lemma trace_re_le_card_mul_l2_opNorm_of_posSemidef
    {A : Matrix n n Complex} (hA : A.PosSemidef) :
    A.trace.re <= (Fintype.card n : Real) * ‖A‖ := by
  rw [trace_re_eq_sum_eigenvalues hA.1,
    posSemidef_l2_opNorm_eq_lambdaMax hA]
  calc
    (∑ i, hA.1.eigenvalues i) <= ∑ _i : n, lambdaMax hA.1 := by
      exact Finset.sum_le_sum fun i _ => eigenvalues_le_lambdaMax hA.1 i
    _ = (Fintype.card n : Real) * lambdaMax hA.1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end TraceBound

section FrobeniusMoment

variable {Omega m n I : Type*} [MeasurableSpace Omega]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype I] [DecidableEq I] [Nonempty m]
  {mu : Measure Omega} [IsProbabilityMeasure mu]

/-- Lean implementation helper.

The row-dimension Frobenius bound for a centered independent sum. -/
lemma centered_sum_norm_sq_le_card_row_variance
    {S : I -> Omega -> Matrix m n Complex}
    (hind : iIndepFun S mu) (hmeas : forall k, Measurable (S k))
    (hcent : forall k, expectation mu (S k) = 0)
    {R : I -> Real} (hbdd : forall k omega, ‖S k omega‖ <= R k) :
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) <=
      (Fintype.card m : Real) *
        ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖ := by
  let C : Real := ∑ k, |R k|
  let Z : Omega -> Matrix m n Complex := fun omega => ∑ k, S k omega
  have hS : forall k, MIntegrable (S k) mu := fun k =>
    MIntegrable.of_bound (hmeas k) |R k| (Filter.Eventually.of_forall fun omega i j =>
      (norm_entry_le_l2_opNorm_rect _ _ _).trans
        ((hbdd k omega).trans (le_abs_self (R k))))
  have hS1 : forall k,
      MIntegrable (fun omega => S k omega * (S k omega)ᴴ) mu := fun k =>
    MIntegrable.of_bound (measurable_mul_conjTranspose_self (hmeas k)) (|R k| * |R k|)
      (Filter.Eventually.of_forall fun omega i j => by
        calc
          ‖(S k omega * (S k omega)ᴴ) i j‖ <= ‖S k omega * (S k omega)ᴴ‖ :=
            norm_entry_le_l2_opNorm_rect _ _ _
          _ <= ‖S k omega‖ * ‖(S k omega)ᴴ‖ := Matrix.l2_opNorm_mul _ _
          _ = ‖S k omega‖ * ‖S k omega‖ := by rw [Matrix.l2_opNorm_conjTranspose]
          _ <= |R k| * |R k| := by
            nlinarith [norm_nonneg (S k omega), hbdd k omega,
              le_abs_self (R k)])
  have hZmeas : Measurable Z := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    change Measurable fun omega => (∑ k, S k omega) i j
    simp_rw [Matrix.sum_apply]
    exact Finset.measurable_sum _ fun k _ =>
      (measurable_entry i j).comp (hmeas k)
  have hZbdd : forall omega, ‖Z omega‖ <= C := by
    intro omega
    calc
      ‖Z omega‖ <= ∑ k, ‖S k omega‖ := norm_sum_le _ _
      _ <= ∑ k, |R k| := Finset.sum_le_sum fun k _ =>
        (hbdd k omega).trans (le_abs_self (R k))
      _ = C := rfl
  have hZ1 : MIntegrable (fun omega => Z omega * (Z omega)ᴴ) mu :=
    MIntegrable.of_bound (measurable_mul_conjTranspose_self hZmeas) (C * C)
      (Filter.Eventually.of_forall fun omega i j => by
        calc
          ‖(Z omega * (Z omega)ᴴ) i j‖ <= ‖Z omega * (Z omega)ᴴ‖ :=
            norm_entry_le_l2_opNorm_rect _ _ _
          _ <= ‖Z omega‖ * ‖(Z omega)ᴴ‖ := Matrix.l2_opNorm_mul _ _
          _ = ‖Z omega‖ * ‖Z omega‖ := by rw [Matrix.l2_opNorm_conjTranspose]
          _ <= C * C := by nlinarith [norm_nonneg (Z omega), hZbdd omega])
  have htraceint : Integrable (fun omega => (Z omega * (Z omega)ᴴ).trace) mu := by
    exact integrable_finsetSum Finset.univ fun i _ => hZ1 i i
  have hfrobint : Integrable (fun omega => frobeniusNorm (Z omega) ^ 2) mu := by
    refine htraceint.re.congr (Filter.Eventually.of_forall fun omega => ?_)
    change ((Z omega * (Z omega)ᴴ).trace).re = frobeniusNorm (Z omega) ^ 2
    rw [trace_mul_conjTranspose_self]
    exact Complex.ofReal_re _
  have hnormint : Integrable (fun omega => ‖Z omega‖ ^ 2) mu := by
    refine Integrable.of_bound
      ((continuous_l2_opNorm.measurable.comp hZmeas).pow_const 2).aestronglyMeasurable
      (C ^ 2) (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (Z omega), hZbdd omega]
  have hfrob_eq :
      (∫ omega, frobeniusNorm (Z omega) ^ 2 ∂mu) =
        ((expectation mu fun omega => Z omega * (Z omega)ᴴ).trace).re := by
    have htr := congrArg Complex.re (expectation_trace hZ1)
    calc
      (∫ omega, frobeniusNorm (Z omega) ^ 2 ∂mu) =
          ∫ omega, ((Z omega * (Z omega)ᴴ).trace).re ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with omega
        rw [trace_mul_conjTranspose_self]
        exact (Complex.ofReal_re _).symm
      _ = (∫ omega, (Z omega * (Z omega)ᴴ).trace ∂mu).re :=
        integral_re htraceint
      _ = ((expectation mu fun omega => Z omega * (Z omega)ᴴ).trace).re := htr
  have hEgram :
      expectation mu (fun omega => Z omega * (Z omega)ᴴ) =
        ∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ) := by
    simpa only [Z] using
      expectation_sum_mul_conjTranspose_of_centered hind hmeas hS hS1 hcent
  let A : Matrix m m Complex :=
    ∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)
  have hApsd : A.PosSemidef := by
    exact posSemidef_matsum Finset.univ fun k =>
      posSemidef_expectation (hS1 k)
        (Filter.Eventually.of_forall fun omega =>
          Matrix.posSemidef_self_mul_conjTranspose (S k omega))
  calc
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) =
        ∫ omega, ‖Z omega‖ ^ 2 ∂mu := by rfl
    _ <= ∫ omega, frobeniusNorm (Z omega) ^ 2 ∂mu := by
      exact integral_mono hnormint hfrobint fun omega => by
        nlinarith [l2_opNorm_le_frobeniusNorm (Z omega),
          norm_nonneg (Z omega), frobeniusNorm_nonneg (Z omega)]
    _ = A.trace.re := by rw [hfrob_eq, hEgram]
    _ <= (Fintype.card m : Real) * ‖A‖ :=
      trace_re_le_card_mul_l2_opNorm_of_posSemidef hApsd
    _ = _ := rfl

/-- Lean implementation helper.

The column-dimension version, obtained by conjugate transposition. -/
lemma centered_sum_norm_sq_le_card_col_variance [Nonempty n]
    {S : I -> Omega -> Matrix m n Complex}
    (hind : iIndepFun S mu) (hmeas : forall k, Measurable (S k))
    (hcent : forall k, expectation mu (S k) = 0)
    {R : I -> Real} (hbdd : forall k omega, ‖S k omega‖ <= R k) :
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) <=
      (Fintype.card n : Real) *
        ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ := by
  let T : I -> Omega -> Matrix n m Complex := fun k omega => (S k omega)ᴴ
  have hindT : iIndepFun T mu :=
    hind.comp (fun _ A => Aᴴ) (fun _ => measurable_conjTranspose_map)
  have hmeasT : forall k, Measurable (T k) := fun k =>
    measurable_conjTranspose_map.comp (hmeas k)
  have hcentT : forall k, expectation mu (T k) = 0 := by
    intro k
    dsimp only [T]
    rw [expectation_conjTranspose, hcent k, Matrix.conjTranspose_zero]
  have hbddT : forall k omega, ‖T k omega‖ <= R k := by
    intro k omega
    dsimp only [T]
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hbdd k omega
  have h := centered_sum_norm_sq_le_card_row_variance
    (S := T) hindT hmeasT hcentT hbddT
  simpa only [T, ← Matrix.conjTranspose_sum,
    Matrix.l2_opNorm_conjTranspose, Matrix.conjTranspose_conjTranspose] using h

/-- Lean implementation helper.

The two one-sided trace estimates combine to the minimum-dimension bound. -/
lemma centered_sum_norm_sq_le_min_card_variance [Nonempty n]
    {S : I -> Omega -> Matrix m n Complex}
    (hind : iIndepFun S mu) (hmeas : forall k, Measurable (S k))
    (hcent : forall k, expectation mu (S k) = 0)
    {R : I -> Real} (hbdd : forall k omega, ‖S k omega‖ <= R k) :
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) <=
      (min (Fintype.card m) (Fintype.card n) : Real) *
        max
          ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
          ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ := by
  have hrow := centered_sum_norm_sq_le_card_row_variance hind hmeas hcent hbdd
  have hcol := centered_sum_norm_sq_le_card_col_variance hind hmeas hcent hbdd
  by_cases hmn : Fintype.card m <= Fintype.card n
  · calc
      (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) <=
          (Fintype.card m : Real) *
            ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖ := hrow
      _ <= (Fintype.card m : Real) *
          max
            ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
            ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ := by
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)
      _ = _ := by
        rw [min_eq_left (by exact_mod_cast hmn :
          (Fintype.card m : Real) <= Fintype.card n)]
  · have hnm : Fintype.card n <= Fintype.card m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
    calc
      (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) <=
          (Fintype.card n : Real) *
            ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ := hcol
      _ <= (Fintype.card n : Real) *
          max
            ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
            ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ := by
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _)
      _ = _ := by
        rw [min_eq_right (by exact_mod_cast hnm :
          (Fintype.card n : Real) <= Fintype.card m)]

end FrobeniusMoment


section DilationSquares

variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {d₁ d₂ : ℕ}

/-- Lean implementation helper.

The expected square function of the Hermitian dilations is the block
diagonal matrix formed by the two rectangular square functions. -/
lemma sum_expectation_hermDilation_sq
    (S : I → Ω → Matrix (Fin d₁) (Fin d₂) ℂ) :
    (∑ k, expectation μ (fun ω => (hermDilation (S k ω)) ^ 2)) =
      Matrix.fromBlocks
        (∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)) 0 0
        (∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)) := by
  rw [← sum_fromBlocks_diagonal]
  apply Finset.sum_congr rfl
  intro k _
  have hpoint : (fun ω => (hermDilation (S k ω)) ^ 2) =
      fun ω => Matrix.fromBlocks
        (S k ω * (S k ω)ᴴ) 0 0 ((S k ω)ᴴ * S k ω) := by
    funext ω
    rw [pow_two]
    exact hermDilation_sq (S k ω)
  rw [hpoint, expectation_fromBlocks_diag]

/-- Lean implementation helper.

Norm form of `sum_expectation_hermDilation_sq`. -/
lemma norm_sum_expectation_hermDilation_sq
    (S : I → Ω → Matrix (Fin d₁) (Fin d₂) ℂ) :
    ‖∑ k, expectation μ (fun ω => (hermDilation (S k ω)) ^ 2)‖ =
      max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
        ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ := by
  rw [sum_expectation_hermDilation_sq]
  exact l2_opNorm_fromBlocks_diagonal _ _

end DilationSquares

section MomentUtilities

variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {d₁ d₂ : ℕ}

/-- Lean implementation helper. -/
lemma maxSummandSq_nonneg
    (S : I → Ω → Matrix (Fin d₁) (Fin d₂) ℂ) :
    0 ≤ maxSummandSq S μ := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
      letI := hI
      simp [maxSummandSq]
  | inr hI =>
      letI := hI
      apply integral_nonneg
      intro ω
      exact (sq_nonneg ‖S (Classical.arbitrary I) ω‖).trans
        (le_ciSup (Finite.bddAbove_range fun k => ‖S k ω‖ ^ 2)
          (Classical.arbitrary I))

end MomentUtilities

section GhostCopy

variable {Omega : Type uOmega} [MeasurableSpace Omega] {mu : Measure Omega}
  [IsProbabilityMeasure mu]
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {d1 d2 : Nat}

/-- Lean implementation helper. -/
def ghostDiff (S : I -> Omega -> Matrix (Fin d1) (Fin d2) Complex)
    (k : I) (p : Omega × Omega) : Matrix (Fin d1) (Fin d2) Complex :=
  S k p.1 - S k p.2

/-- Lean implementation helper. -/
lemma measurable_ghostDiff {S : I -> Omega -> Matrix (Fin d1) (Fin d2) Complex}
    (hmeas : forall k, Measurable (S k)) (k : I) :
    Measurable (ghostDiff S k) := by
  exact (hmeas k |>.comp measurable_fst).sub (hmeas k |>.comp measurable_snd)

/-- Lean implementation helper. -/
lemma ghostDiff_symmetric {S : I -> Omega -> Matrix (Fin d1) (Fin d2) Complex}
    (hmeas : forall k, Measurable (S k)) (k : I) :
    IsSymmetricRV (ghostDiff S k) (mu.prod mu) := by
  let D := ghostDiff S k
  have hD : Measurable D := measurable_ghostDiff hmeas k
  have hswap := Measure.measurePreserving_swap (μ := mu) (ν := mu)
  rw [IsSymmetricRV]
  calc
    (mu.prod mu).map D = ((mu.prod mu).map Prod.swap).map D := by
      rw [hswap.map_eq]
    _ = (mu.prod mu).map (D ∘ Prod.swap) := by
      rw [Measure.map_map hD hswap.measurable]
    _ = (mu.prod mu).map (fun p => -(D p)) := by
      congr 1
      funext p
      simp [D, ghostDiff]

/-- Lean implementation helper. -/
lemma iIndepFun_ghostDiff {S : I -> Omega -> Matrix (Fin d1) (Fin d2) Complex}
    (hind : iIndepFun S mu) (hmeas : forall k, Measurable (S k)) :
    iIndepFun (ghostDiff S) (mu.prod mu) := by
  let E := Matrix (Fin d1) (Fin d2) Complex
  let Phi : Omega -> (I -> E) := fun omega k => S k omega
  let nu : I -> Measure E := fun k => mu.map (S k)
  let rho : Measure (I -> E) := Measure.pi nu
  let sigma : Measure (I -> E × E) := Measure.pi fun k => (nu k).prod (nu k)
  letI (k : I) : IsProbabilityMeasure (nu k) :=
    Measure.isProbabilityMeasure_map (hmeas k).aemeasurable
  have hPhilaw : mu.map Phi = rho := by
    simpa only [Phi, rho, nu] using
      hind.map_fun_eq_pi_map (fun k => (hmeas k).aemeasurable)
  have hPhimp : MeasurePreserving Phi mu rho :=
    ⟨measurable_pi_lambda _ hmeas, hPhilaw⟩
  let e := MeasurableEquiv.arrowProdEquivProdArrow E E I
  have he : MeasurePreserving e sigma (rho.prod rho) := by
    simpa only [e, sigma, rho] using
      (measurePreserving_arrowProdEquivProdArrow E E I nu nu)
  let T : Omega × Omega -> (I -> E × E) :=
    fun p k => (S k p.1, S k p.2)
  have hT : MeasurePreserving T (mu.prod mu) sigma := by
    have hp := hPhimp.prod hPhimp
    have hc := he.symm e |>.comp hp
    change MeasurePreserving T (mu.prod mu) sigma at hc
    exact hc
  let delta : I -> (I -> E × E) -> E := fun k q => (q k).1 - (q k).2
  have hpair : iIndepFun (fun k (q : I -> E × E) => q k) sigma := by
    exact iIndepFun_pi (μ := fun k => (nu k).prod (nu k))
      (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
  have hdelta : iIndepFun delta sigma := by
    exact hpair.comp (fun _ z => z.1 - z.2)
      (fun _ => measurable_fst.sub measurable_snd)
  have hdeltaMeas : forall k, Measurable (delta k) := fun k =>
    (measurable_fst.comp (measurable_pi_apply k)).sub
      (measurable_snd.comp (measurable_pi_apply k))
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun k => (measurable_ghostDiff hmeas k).aemeasurable)]
  have hjointMeas : Measurable (fun q => fun k => delta k q) :=
    measurable_pi_lambda _ hdeltaMeas
  have hjoint : sigma.map (fun q => fun k => delta k q) =
      Measure.pi fun k => sigma.map (delta k) :=
    hdelta.map_fun_eq_pi_map (fun k => (hdeltaMeas k).aemeasurable)
  calc
    (mu.prod mu).map (fun p k => ghostDiff S k p) =
        (mu.prod mu).map ((fun q => fun k => delta k q) ∘ T) := by rfl
    _ = sigma.map (fun q => fun k => delta k q) := by
      rw [← Measure.map_map hjointMeas hT.measurable, hT.map_eq]
    _ = Measure.pi (fun k => sigma.map (delta k)) := hjoint
    _ = Measure.pi (fun k => (mu.prod mu).map (ghostDiff S k)) := by
      congr 1
      funext k
      calc
        sigma.map (delta k) = ((mu.prod mu).map T).map (delta k) := by
          rw [hT.map_eq]
        _ = (mu.prod mu).map ((delta k) ∘ T) := by
          rw [Measure.map_map (hdeltaMeas k) hT.measurable]
        _ = (mu.prod mu).map (ghostDiff S k) := by rfl

/-- Lean implementation helper. -/
lemma expectation_comp_fst
    {Z : Omega -> Matrix (Fin d1) (Fin d2) Complex} (hZ : MIntegrable Z mu) :
    expectation (mu.prod mu) (fun p => Z p.1) = expectation mu Z := by
  ext i j
  rw [expectation_apply, expectation_apply,
    MeasureTheory.integral_prod _ ((hZ i j).comp_fst mu)]
  simp

/-- Lean implementation helper. -/
lemma expectation_comp_snd
    {Z : Omega -> Matrix (Fin d1) (Fin d2) Complex} (hZ : MIntegrable Z mu) :
    expectation (mu.prod mu) (fun p => Z p.2) = expectation mu Z := by
  ext i j
  rw [expectation_apply, expectation_apply,
    MeasureTheory.integral_prod _ ((hZ i j).comp_snd mu)]
  simp

/-- Lean implementation helper. -/
lemma ghostDiff_rowVariance
    {S : Omega -> Matrix (Fin d1) (Fin d2) Complex}
    (hmeas : Measurable S) (hS : MIntegrable S mu)
    (hSS : MIntegrable (fun omega => S omega * (S omega)ᴴ) mu)
    (hcent : expectation mu S = 0) :
    expectation (mu.prod mu)
        (fun p => ghostDiff (I := Unit) (fun _ => S) () p *
          (ghostDiff (I := Unit) (fun _ => S) () p)ᴴ) =
      2 • expectation mu (fun omega => S omega * (S omega)ᴴ) := by
  let X : Omega × Omega -> Matrix (Fin d1) (Fin d2) Complex := fun p => S p.1
  let Y : Omega × Omega -> Matrix (Fin d1) (Fin d2) Complex := fun p => S p.2
  have hX : MIntegrable X (mu.prod mu) := fun i j => (hS i j).comp_fst mu
  have hY : MIntegrable Y (mu.prod mu) := fun i j => (hS i j).comp_snd mu
  have hXX : MIntegrable (fun p => X p * (X p)ᴴ) (mu.prod mu) :=
    fun i j => (hSS i j).comp_fst mu
  have hYY : MIntegrable (fun p => Y p * (Y p)ᴴ) (mu.prod mu) :=
    fun i j => (hSS i j).comp_snd mu
  have hbase : IndepFun X Y (mu.prod mu) := by
    simpa only [X, Y] using
      (indepFun_prod (μ := mu) (ν := mu) hmeas hmeas)
  have hixy : IndepFun X (fun p => (Y p)ᴴ) (mu.prod mu) := by
    simpa [Function.comp_def] using
      hbase.comp measurable_id measurable_conjTranspose_map
  have hiyx : IndepFun Y (fun p => (X p)ᴴ) (mu.prod mu) := by
    simpa [Function.comp_def] using
      hbase.symm.comp measurable_id measurable_conjTranspose_map
  have hXY : MIntegrable (fun p => X p * (Y p)ᴴ) (mu.prod mu) :=
    MIntegrable.mul_of_indepFun hixy hX hY.conjTranspose
  have hYX : MIntegrable (fun p => Y p * (X p)ᴴ) (mu.prod mu) :=
    MIntegrable.mul_of_indepFun hiyx hY hX.conjTranspose
  have hEX : expectation (mu.prod mu) X = 0 := by
    rw [expectation_comp_fst hS, hcent]
  have hEY : expectation (mu.prod mu) Y = 0 := by
    rw [expectation_comp_snd hS, hcent]
  have hEXX : expectation (mu.prod mu) (fun p => X p * (X p)ᴴ) =
      expectation mu (fun omega => S omega * (S omega)ᴴ) :=
    expectation_comp_fst hSS
  have hEYY : expectation (mu.prod mu) (fun p => Y p * (Y p)ᴴ) =
      expectation mu (fun omega => S omega * (S omega)ᴴ) :=
    expectation_comp_snd hSS
  have hEXY : expectation (mu.prod mu) (fun p => X p * (Y p)ᴴ) = 0 := by
    have hh := expectation_mul_of_indepFun hixy
      (hmeas.comp measurable_fst)
      (measurable_conjTranspose_map.comp (hmeas.comp measurable_snd))
      hX hY.conjTranspose
    have hEcY : expectation (mu.prod mu) (fun p => (Y p)ᴴ) = 0 := by
      rw [expectation_conjTranspose, hEY, Matrix.conjTranspose_zero]
    simpa [hEX, hEcY] using hh
  have hEYX : expectation (mu.prod mu) (fun p => Y p * (X p)ᴴ) = 0 := by
    have hh := expectation_mul_of_indepFun hiyx
      (hmeas.comp measurable_snd)
      (measurable_conjTranspose_map.comp (hmeas.comp measurable_fst))
      hY hX.conjTranspose
    have hEcX : expectation (mu.prod mu) (fun p => (X p)ᴴ) = 0 := by
      rw [expectation_conjTranspose, hEX, Matrix.conjTranspose_zero]
    simpa [hEY, hEcX] using hh
  change expectation (mu.prod mu) (fun p => (X p - Y p) * (X p - Y p)ᴴ) = _
  have hexpand : (fun p => (X p - Y p) * (X p - Y p)ᴴ) =
      fun p => (X p * (X p)ᴴ - X p * (Y p)ᴴ) -
        (Y p * (X p)ᴴ - Y p * (Y p)ᴴ) := by
    funext p
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [hexpand,
    expectation_sub (hXX.sub hXY) (hYX.sub hYY),
    expectation_sub hXX hXY,
    expectation_sub hYX hYY,
    hEXX, hEYY, hEXY, hEYX]
  module

/-- Lean implementation helper. -/
lemma ghostDiff_colVariance
    {S : Omega -> Matrix (Fin d1) (Fin d2) Complex}
    (hmeas : Measurable S) (hS : MIntegrable S mu)
    (hSS : MIntegrable (fun omega => (S omega)ᴴ * S omega) mu)
    (hcent : expectation mu S = 0) :
    expectation (mu.prod mu)
        (fun p => (ghostDiff (I := Unit) (fun _ => S) () p)ᴴ *
          ghostDiff (I := Unit) (fun _ => S) () p) =
      2 • expectation mu (fun omega => (S omega)ᴴ * S omega) := by
  let T : Omega -> Matrix (Fin d2) (Fin d1) Complex := fun omega => (S omega)ᴴ
  have hTm : Measurable T := measurable_conjTranspose_map.comp hmeas
  have hTint : MIntegrable T mu := hS.conjTranspose
  have hTT : MIntegrable (fun omega => T omega * (T omega)ᴴ) mu := by
    simpa [T] using hSS
  have hTcent : expectation mu T = 0 := by
    rw [show T = fun omega => (S omega)ᴴ from rfl,
      expectation_conjTranspose, hcent, Matrix.conjTranspose_zero]
  have h := ghostDiff_rowVariance (mu := mu) (S := T) hTm hTint hTT hTcent
  simpa [T, ghostDiff, Matrix.conjTranspose_sub] using h

/-- Lean implementation helper. -/
lemma ghostDiff_variances_of_bound
    {S : I -> Omega -> Matrix (Fin d1) (Fin d2) Complex}
    (hmeas : forall k, Measurable (S k))
    (hcent : forall k, expectation mu (S k) = 0)
    {R : I -> Real} (hbd : forall k omega, ‖S k omega‖ <= R k) (k : I) :
    expectation (mu.prod mu)
        (fun p => ghostDiff S k p * (ghostDiff S k p)ᴴ) =
        2 • expectation mu (fun omega => S k omega * (S k omega)ᴴ) ∧
      expectation (mu.prod mu)
        (fun p => (ghostDiff S k p)ᴴ * ghostDiff S k p) =
        2 • expectation mu (fun omega => (S k omega)ᴴ * S k omega) := by
  have hSint : MIntegrable (S k) mu :=
    mintegrable_rect_of_norm_bound (hmeas k) (hbd k)
  have hrow : MIntegrable (fun omega => S k omega * (S k omega)ᴴ) mu := by
    refine MIntegrable.of_bound (measurable_mul_conjTranspose_self (hmeas k))
      ((R k) ^ 2) (Filter.Eventually.of_forall fun omega i j => ?_)
    calc
      ‖(S k omega * (S k omega)ᴴ) i j‖ <=
          ‖S k omega * (S k omega)ᴴ‖ := norm_entry_le_l2_opNorm_rect _ _ _
      _ <= ‖S k omega‖ * ‖(S k omega)ᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖S k omega‖ * ‖S k omega‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]
      _ <= (R k) ^ 2 := by
        nlinarith [norm_nonneg (S k omega), hbd k omega]
  have hcol : MIntegrable (fun omega => (S k omega)ᴴ * S k omega) mu := by
    refine MIntegrable.of_bound (measurable_conjTranspose_mul_self (hmeas k))
      ((R k) ^ 2) (Filter.Eventually.of_forall fun omega i j => ?_)
    calc
      ‖((S k omega)ᴴ * S k omega) i j‖ <=
          ‖(S k omega)ᴴ * S k omega‖ := norm_entry_le_l2_opNorm_rect _ _ _
      _ <= ‖(S k omega)ᴴ‖ * ‖S k omega‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖S k omega‖ * ‖S k omega‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]
      _ <= (R k) ^ 2 := by
        nlinarith [norm_nonneg (S k omega), hbd k omega]
  constructor
  · simpa only [ghostDiff] using
      (ghostDiff_rowVariance (mu := mu) (S := S k) (hmeas k)
        hSint hrow (hcent k))
  · simpa only [ghostDiff] using
      (ghostDiff_colVariance (mu := mu) (S := S k) (hmeas k)
        hSint hcol (hcent k))

/-- Lean implementation helper. -/
lemma ghost_l2_symmetrization
    {S : I -> Omega -> Matrix (Fin d1) (Fin d2) Complex}
    (hmeas : forall k, Measurable (S k))
    (hcent : forall k, expectation mu (S k) = 0)
    {R : I -> Real} (hbd : forall k omega, ‖S k omega‖ <= R k) :
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) <=
      ∫ p : Omega × Omega, ‖∑ k, ghostDiff S k p‖ ^ 2 ∂(mu.prod mu) := by
  let Z : Omega -> Matrix (Fin d1) (Fin d2) Complex := fun omega => ∑ k, S k omega
  let B : Real := ∑ k, |R k|
  have hB0 : 0 <= B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hZm : Measurable Z := by
    simpa only [Z] using
      (Finset.measurable_sum Finset.univ fun k _ => hmeas k)
  have hZbd : forall omega, ‖Z omega‖ <= B := by
    intro omega
    calc
      ‖Z omega‖ <= ∑ k, ‖S k omega‖ := norm_sum_le _ _
      _ <= ∑ k, |R k| := Finset.sum_le_sum fun k _ =>
        (hbd k omega).trans (le_abs_self (R k))
      _ = B := rfl
  have hSint : forall k, MIntegrable (S k) mu := fun k =>
    mintegrable_rect_of_norm_bound (hmeas k) (hbd k)
  have hZint : MIntegrable Z mu := fun i j => by
    simpa only [Z, Matrix.sum_apply] using
      (integrable_finsetSum Finset.univ fun k _ => hSint k i j)
  have hEZ : expectation mu Z = 0 := by
    rw [show expectation mu Z = ∑ k, expectation mu (S k) by
      exact expectation_finsetSum Finset.univ fun k _ => hSint k]
    simp [hcent]
  have hZsq : Integrable (fun omega => ‖Z omega‖ ^ 2) mu := by
    refine Integrable.of_bound
      ((continuous_l2_opNorm.measurable.comp hZm).pow_const 2).aestronglyMeasurable
      (B ^ 2) (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (Z omega), hZbd omega]
  let D : Omega × Omega -> Matrix (Fin d1) (Fin d2) Complex :=
    fun p => Z p.1 - Z p.2
  have hDm : Measurable D :=
    (hZm.comp measurable_fst).sub (hZm.comp measurable_snd)
  have hDbd : forall p, ‖D p‖ <= 2 * B := by
    intro p
    calc
      ‖D p‖ <= ‖Z p.1‖ + ‖Z p.2‖ := norm_sub_le _ _
      _ <= B + B := add_le_add (hZbd p.1) (hZbd p.2)
      _ = 2 * B := by ring
  have hDsq : Integrable (fun p => ‖D p‖ ^ 2) (mu.prod mu) := by
    refine Integrable.of_bound
      ((continuous_l2_opNorm.measurable.comp hDm).pow_const 2).aestronglyMeasurable
      ((2 * B) ^ 2) (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (D p), hDbd p]
  have hpoint : forall omega, ‖Z omega‖ ^ 2 <=
      ∫ omega', ‖D (omega, omega')‖ ^ 2 ∂mu := by
    intro omega
    let V : Omega -> Matrix (Fin d1) (Fin d2) Complex :=
      fun omega' => Z omega - Z omega'
    have hVint : MIntegrable V mu := (MIntegrable.const (Z omega)).sub hZint
    have hEV : expectation mu V = Z omega := by
      rw [show V = fun omega' => Z omega - Z omega' from rfl,
        expectation_sub (MIntegrable.const _) hZint,
        expectation_const, hEZ, sub_zero]
    have hVnorm : Integrable (fun omega' => ‖V omega'‖) mu := by
      refine Integrable.of_bound
        (continuous_l2_opNorm.measurable.comp
          (measurable_const.sub hZm)).aestronglyMeasurable
        (2 * B) (Filter.Eventually.of_forall fun omega' => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans
        ((add_le_add (hZbd omega) (hZbd omega')).trans_eq (by ring))
    have hVsq : Integrable (fun omega' => ‖V omega'‖ ^ 2) mu := by
      refine Integrable.of_bound
        ((continuous_l2_opNorm.measurable.comp
          (measurable_const.sub hZm)).pow_const 2).aestronglyMeasurable
        ((2 * B) ^ 2) (Filter.Eventually.of_forall fun omega' => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hvbd : ‖V omega'‖ <= 2 * B :=
        (norm_sub_le _ _).trans
          ((add_le_add (hZbd omega) (hZbd omega')).trans_eq (by ring))
      nlinarith [norm_nonneg (V omega')]
    have hj := norm_expectation_le hVint hVnorm
    rw [hEV] at hj
    have hc := integral_sqrt_mul_le_sqrt_integral_mul
      (mu := mu) (M := fun _ : Omega => 1) (Y := fun omega' => ‖V omega'‖ ^ 2)
      (integrable_const 1) hVsq (fun _ => by norm_num) (fun _ => sq_nonneg _)
    simp only [one_mul, Real.sqrt_sq (norm_nonneg _), integral_const,
      probReal_univ, one_smul, one_mul] at hc
    have hinner0 : 0 <= ∫ omega', ‖V omega'‖ ^ 2 ∂mu :=
      integral_nonneg fun _ => sq_nonneg _
    have hsqrt0 := Real.sqrt_nonneg (∫ omega', ‖V omega'‖ ^ 2 ∂mu)
    have hsqrtSq := Real.sq_sqrt hinner0
    change ‖Z omega‖ ^ 2 <= ∫ omega', ‖V omega'‖ ^ 2 ∂mu
    nlinarith [norm_nonneg (Z omega)]
  have hi := integral_mono hZsq hDsq.integral_prod_left hpoint
  rw [← MeasureTheory.integral_prod _ hDsq] at hi
  simpa only [Z, D, ghostDiff, Finset.sum_sub_distrib] using hi

/-- Lean implementation helper. -/
lemma maxSummandSq_ghostDiff_le
    {S : I -> Omega -> Matrix (Fin d1) (Fin d2) Complex}
    (hmeas : forall k, Measurable (S k))
    {R : I -> Real} (hbd : forall k omega, ‖S k omega‖ <= R k) :
    maxSummandSq (ghostDiff S) (mu.prod mu) <= 4 * maxSummandSq S mu := by
  cases isEmpty_or_nonempty I with
  | inl hI =>
      simp [maxSummandSq]
  | inr hI =>
      let Q : Omega -> Real := fun omega => ⨆ k, ‖S k omega‖ ^ 2
      let QD : Omega × Omega -> Real :=
        fun p => ⨆ k, ‖ghostDiff S k p‖ ^ 2
      let C : Real := ∑ k, (R k) ^ 2
      have hC0 : 0 <= C := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hQm : Measurable Q := Measurable.iSup fun k =>
        (continuous_l2_opNorm.measurable.comp (hmeas k)).pow_const 2
      have hQ0 : forall omega, 0 <= Q omega := by
        intro omega
        exact (sq_nonneg ‖S (Classical.arbitrary I) omega‖).trans
          (le_ciSup (Finite.bddAbove_range fun k => ‖S k omega‖ ^ 2)
            (Classical.arbitrary I))
      have hQbd : forall omega, Q omega <= C := by
        intro omega
        apply ciSup_le
        intro k
        have hk : ‖S k omega‖ ^ 2 <= (R k) ^ 2 := by
          nlinarith [norm_nonneg (S k omega), hbd k omega]
        exact hk.trans (Finset.single_le_sum (fun i _ => sq_nonneg (R i))
          (Finset.mem_univ k))
      have hQint : Integrable Q mu := by
        refine Integrable.of_bound hQm.aestronglyMeasurable C
          (Filter.Eventually.of_forall fun omega => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hQ0 omega)]
        exact hQbd omega
      have hQDm : Measurable QD := Measurable.iSup fun k =>
        (continuous_l2_opNorm.measurable.comp
          (measurable_ghostDiff hmeas k)).pow_const 2
      have hQD0 : forall p, 0 <= QD p := by
        intro p
        exact (sq_nonneg ‖ghostDiff S (Classical.arbitrary I) p‖).trans
          (le_ciSup
            (Finite.bddAbove_range fun k => ‖ghostDiff S k p‖ ^ 2)
            (Classical.arbitrary I))
      have hpoint : forall p, QD p <= 2 * Q p.1 + 2 * Q p.2 := by
        intro p
        apply ciSup_le
        intro k
        have hk1 : ‖S k p.1‖ ^ 2 <= Q p.1 :=
          le_ciSup (Finite.bddAbove_range fun j => ‖S j p.1‖ ^ 2) k
        have hk2 : ‖S k p.2‖ ^ 2 <= Q p.2 :=
          le_ciSup (Finite.bddAbove_range fun j => ‖S j p.2‖ ^ 2) k
        have hsub := norm_sub_le (S k p.1) (S k p.2)
        change ‖S k p.1 - S k p.2‖ ^ 2 <= _
        nlinarith [norm_nonneg (S k p.1), norm_nonneg (S k p.2),
          norm_nonneg (S k p.1 - S k p.2),
          sq_nonneg (‖S k p.1‖ - ‖S k p.2‖)]
      have hQDbd : forall p, QD p <= 4 * C := by
        intro p
        exact (hpoint p).trans (by nlinarith [hQbd p.1, hQbd p.2])
      have hQDint : Integrable QD (mu.prod mu) := by
        refine Integrable.of_bound hQDm.aestronglyMeasurable (4 * C)
          (Filter.Eventually.of_forall fun p => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hQD0 p)]
        exact hQDbd p
      have hRint : Integrable (fun p : Omega × Omega =>
          2 * Q p.1 + 2 * Q p.2) (mu.prod mu) :=
        (hQint.comp_fst mu |>.const_mul 2).add
          (hQint.comp_snd mu |>.const_mul 2)
      have hi := integral_mono hQDint hRint hpoint
      have hfst : (∫ p : Omega × Omega, Q p.1 ∂(mu.prod mu)) = ∫ omega, Q omega ∂mu := by
        rw [MeasureTheory.integral_prod _ (hQint.comp_fst mu)]
        simp
      have hsnd : (∫ p : Omega × Omega, Q p.2 ∂(mu.prod mu)) = ∫ omega, Q omega ∂mu := by
        rw [MeasureTheory.integral_prod _ (hQint.comp_snd mu)]
        simp
      rw [integral_add (hQint.comp_fst mu |>.const_mul 2)
        (hQint.comp_snd mu |>.const_mul 2),
        integral_const_mul, integral_const_mul, hfst, hsnd] at hi
      dsimp only [Q, QD] at hi
      dsimp only [maxSummandSq]
      nlinarith



end GhostCopy

section SymmetricLargeDimension

variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]
variable {I : Type uI} [Fintype I] [DecidableEq I] [Nonempty I]
variable {d₁ d₂ : ℕ} [Nonempty (Fin d₁)] [Nonempty (Fin d₂)]

/-- Lean implementation helper. -/
private lemma measurable_matrix_family_sum_norm_sq : Measurable
    (fun x : I → Matrix (Fin d₁) (Fin d₂) ℂ => ‖∑ k, x k‖ ^ 2) := by
  fun_prop

/-- Lean implementation helper. -/
private lemma measurable_matrix_mul_local
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    {f : Ω → Matrix a b ℂ} {g : Ω → Matrix b c ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun ω => f ω * g ω := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  rw [show (fun ω => (f ω * g ω) i j) =
    fun ω => ∑ k, f ω i k * g ω k j from funext fun ω => Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_entry i k).comp hf).mul ((measurable_entry k j).comp hg)

/-- Lean implementation helper.

Reflection plus deterministic Rademacher integration. -/
lemma symmetric_expect_sq_le_square_function
    {S : I → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (h_indep : iIndepFun S μ) (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) μ)
    {R : I → ℝ} (h_bdd : ∀ k ω, ‖S k ω‖ ≤ R k) :
    ∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ ≤
      2 * (1 + Real.log (d₁ + d₂)) *
        ∫ ω, max ‖∑ k, S k ω * (S k ω)ᴴ‖
          ‖∑ k, (S k ω)ᴴ * S k ω‖ ∂μ := by
  classical
  let qsign : (I → Bool) → Ω → ℝ := fun b ω =>
    ‖∑ k, boolSign (b k) • S k ω‖ ^ 2
  let vsq : Ω → ℝ := fun ω =>
    max ‖∑ k, S k ω * (S k ω)ᴴ‖
      ‖∑ k, (S k ω)ᴴ * S k ω‖
  let Csum : ℝ := (∑ k, |R k|) ^ 2
  let Csq : ℝ := ∑ k, (R k) ^ 2
  have hsign_meas : ∀ b : I → Bool, Measurable
      (fun ω => ∑ k, boolSign (b k) • S k ω) := by
    intro b
    exact Finset.measurable_sum Finset.univ fun k _ =>
      measurable_const.smul (h_meas k)
  have hqsign_meas : ∀ b, Measurable (qsign b) := fun b =>
    (continuous_l2_opNorm.measurable.comp (hsign_meas b)).pow_const 2
  have hsigned_bound : ∀ (b : I → Bool) ω,
      ‖∑ k, boolSign (b k) • S k ω‖ ≤ ∑ k, |R k| := by
    intro b ω
    calc
      ‖∑ k, boolSign (b k) • S k ω‖
          ≤ ∑ k, ‖boolSign (b k) • S k ω‖ := norm_sum_le _ _
      _ = ∑ k, ‖S k ω‖ := by
        apply Finset.sum_congr rfl
        intro k _
        cases hb : b k <;> simp [boolSign, hb]
      _ ≤ ∑ k, |R k| := by
        apply Finset.sum_le_sum
        intro k _
        exact (h_bdd k ω).trans (le_abs_self _)
  have hqsign_int : ∀ b, Integrable (qsign b) μ := by
    intro b
    refine Integrable.of_bound (hqsign_meas b).aestronglyMeasurable Csum
      (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only [qsign, Csum]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hsigned_bound b ω,
      norm_nonneg (∑ k, boolSign (b k) • S k ω),
      Finset.sum_nonneg (s := Finset.univ) (fun k _ => abs_nonneg (R k))]
  have hleft_int : Integrable
      (fun ω => (Fintype.card (I → Bool) : ℝ)⁻¹ *
        ∑ b : I → Bool, qsign b ω) μ :=
    (integrable_finsetSum Finset.univ fun b _ => hqsign_int b).const_mul _
  have hmul_meas : ∀ k, Measurable (fun ω => S k ω * (S k ω)ᴴ) :=
    fun k => measurable_mul_conjTranspose_self (h_meas k)
  have hmul'_meas : ∀ k, Measurable (fun ω => (S k ω)ᴴ * S k ω) :=
    fun k => measurable_conjTranspose_mul_self (h_meas k)
  have hvsq_meas : Measurable vsq := by
    dsimp only [vsq]
    exact ((continuous_l2_opNorm.measurable.comp
      (Finset.measurable_sum Finset.univ fun k _ => hmul_meas k)).max
      (continuous_l2_opNorm.measurable.comp
        (Finset.measurable_sum Finset.univ fun k _ => hmul'_meas k)))
  have hvsq_nonneg : ∀ ω, 0 ≤ vsq ω := fun ω =>
    (norm_nonneg _).trans (le_max_left _ _)
  have hvsq_bound : ∀ ω, vsq ω ≤ Csq := by
    intro ω
    dsimp only [vsq, Csq]
    apply max_le
    · calc
        ‖∑ k, S k ω * (S k ω)ᴴ‖
            ≤ ∑ k, ‖S k ω * (S k ω)ᴴ‖ := norm_sum_le _ _
        _ = ∑ k, ‖S k ω‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← (l2_opNorm_sq_eq (S k ω)).1]
        _ ≤ ∑ k, (R k) ^ 2 := by
          apply Finset.sum_le_sum
          intro k _
          nlinarith [norm_nonneg (S k ω), h_bdd k ω]
    · calc
        ‖∑ k, (S k ω)ᴴ * S k ω‖
            ≤ ∑ k, ‖(S k ω)ᴴ * S k ω‖ := norm_sum_le _ _
        _ = ∑ k, ‖S k ω‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← (l2_opNorm_sq_eq (S k ω)).2]
        _ ≤ ∑ k, (R k) ^ 2 := by
          apply Finset.sum_le_sum
          intro k _
          nlinarith [norm_nonneg (S k ω), h_bdd k ω]
  have hvsq_int : Integrable vsq μ := by
    refine Integrable.of_bound hvsq_meas.aestronglyMeasurable Csq
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hvsq_nonneg ω)]
    exact hvsq_bound ω
  have hpoint : ∀ ω,
      (Fintype.card (I → Bool) : ℝ)⁻¹ *
          ∑ b : I → Bool, qsign b ω ≤
        2 * (1 + Real.log (d₁ + d₂)) * vsq ω := by
    intro ω
    have hr := bool_rademacher_rect_expect_sq_upper
      (A := fun k => S k ω)
    have hintb : Integrable (fun b : I → Bool =>
        ‖∑ k, boolSign (b k) • S k ω‖ ^ 2)
        (Measure.pi fun _ : I => boolRademacherMeasure) := Integrable.of_finite
    have havg :
        (∫ b : I → Bool, ‖∑ k, boolSign (b k) • S k ω‖ ^ 2
          ∂Measure.pi fun _ : I => boolRademacherMeasure) =
          (Fintype.card (I → Bool) : ℝ)⁻¹ *
            ∑ b : I → Bool, qsign b ω := by
      rw [integral_fintype hintb]
      simp_rw [boolRademacher_pi_singleton]
      simp only [smul_eq_mul, Finset.mul_sum, qsign]
    rw [havg] at hr
    dsimp only [vsq]
    nlinarith
  have hint := integral_mono hleft_int
    ((hvsq_int.const_mul (2 * (1 + Real.log (d₁ + d₂))))) hpoint
  have hreflect : ∀ b : I → Bool,
      (∫ ω, qsign b ω ∂μ) =
        ∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ := by
    intro b
    simpa only [qsign, signFlip, boolSign, ite_smul, one_smul, neg_one_smul] using
      integral_signFlip_eq_of_symmetric h_indep h_meas h_symm b
        (measurable_matrix_family_sum_norm_sq
          (I := I) (d₁ := d₁) (d₂ := d₂))
  rw [integral_const_mul,
    integral_finsetSum Finset.univ (fun b _ => hqsign_int b)] at hint
  simp_rw [hreflect] at hint
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hint
  rw [integral_const_mul] at hint
  have hcard : (Fintype.card (I → Bool) : ℝ) ≠ 0 := by positivity
  simpa [vsq, inv_mul_cancel₀ hcard] using hint

end SymmetricLargeDimension

section SymmetricLargeDimension

variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]
variable {I : Type uI} [Fintype I] [DecidableEq I] [Nonempty I]
variable {d₁ d₂ : ℕ} [Nonempty (Fin d₁)] [Nonempty (Fin d₂)]

/-- Lean implementation helper.

The positive-square Rosenthal step for Hermitian dilations. -/
lemma square_function_integral_le_rosenthal
    {S : I → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (h_indep : iIndepFun S μ) (h_meas : ∀ k, Measurable (S k))
    {R : I → ℝ} (h_bdd : ∀ k ω, ‖S k ω‖ ≤ R k) :
    (∫ ω, max ‖∑ k, S k ω * (S k ω)ᴴ‖
        ‖∑ k, (S k ω)ᴴ * S k ω‖ ∂μ) ≤
      2 * max
        ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
        ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ +
      8 * Real.exp 1 * maxSummandSq S μ * Real.log (d₁ + d₂) := by
  classical
  let W : I → Ω → Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) ℂ :=
    fun k ω => (hermDilation (S k ω)) ^ 2
  let Csq : ℝ := ∑ k, (R k) ^ 2
  have hWmeas : ∀ k, Measurable (W k) := by
    intro k
    dsimp only [W]
    simpa only [pow_two, Function.comp_apply] using measurable_matrix_mul_local
      (measurable_hermDilation_fun.comp (h_meas k))
      (measurable_hermDilation_fun.comp (h_meas k))
  have hHherm : ∀ k ω, (hermDilation (S k ω)).IsHermitian := fun k ω =>
    isHermitian_hermDilation (S k ω)
  have hWpsd : ∀ k ω, (W k ω).PosSemidef := by
    intro k ω
    dsimp only [W]
    rw [pow_two]
    exact posSemidef_sq (hHherm k ω)
  have hWherm : ∀ k ω, (W k ω).IsHermitian := fun k ω => (hWpsd k ω).1
  have hWmin : ∀ k ω, 0 ≤ lambdaMin (hWherm k ω) := fun k ω =>
    le_lambdaMin _ fun i => (hWpsd k ω).eigenvalues_nonneg i
  have hWnorm : ∀ k ω, ‖W k ω‖ = ‖S k ω‖ ^ 2 := by
    intro k ω
    dsimp only [W]
    rw [pow_two]
    have heq : hermDilation (S k ω) * hermDilation (S k ω) =
        (hermDilation (S k ω))ᴴ * hermDilation (S k ω) := by
      rw [(hHherm k ω).eq]
    rw [heq, ← (l2_opNorm_sq_eq (hermDilation (S k ω))).2,
      l2_opNorm_hermDilation]
  have hWint : ∀ k, MIntegrable (W k) μ := by
    intro k
    refine MIntegrable.of_bound (hWmeas k) ((R k) ^ 2)
      (Filter.Eventually.of_forall fun ω i j => ?_)
    calc
      ‖W k ω i j‖ ≤ ‖W k ω‖ := norm_entry_le_l2_opNorm _ _ _
      _ = ‖S k ω‖ ^ 2 := hWnorm k ω
      _ ≤ (R k) ^ 2 := by
        nlinarith [norm_nonneg (S k ω), h_bdd k ω]
  have hmap : Measurable (fun A : Matrix (Fin d₁) (Fin d₂) ℂ =>
      (hermDilation A) ^ 2) := by
    rw [show (fun A : Matrix (Fin d₁) (Fin d₂) ℂ => (hermDilation A) ^ 2) =
      fun A => hermDilation A * hermDilation A by funext A; rw [pow_two]]
    exact measurable_matrix_mul_local measurable_hermDilation_fun measurable_hermDilation_fun
  have hWind : iIndepFun W μ := by
    exact h_indep.comp (fun _ A => (hermDilation A) ^ 2) (fun _ => hmap)
  have hWmax : ∀ k ω, lambdaMax (hWherm k ω) ≤ Csq := by
    intro k ω
    rw [← posSemidef_l2_opNorm_eq_lambdaMax (hWpsd k ω), hWnorm]
    have hsq : ‖S k ω‖ ^ 2 ≤ (R k) ^ 2 := by
      nlinarith [norm_nonneg (S k ω), h_bdd k ω]
    exact hsq.trans (Finset.single_le_sum (fun j _ => sq_nonneg (R j))
      (Finset.mem_univ k))
  have hsupint : Integrable (fun ω => Finset.univ.sup' Finset.univ_nonempty
      (fun k => lambdaMax (hWherm k ω))) μ := by
    refine Integrable.of_bound ?_ Csq
      (Filter.Eventually.of_forall fun ω => ?_)
    · have hm := Finset.measurable_sup' (s := (Finset.univ : Finset I))
          Finset.univ_nonempty
          (f := fun k (ω : Ω) => lambdaMax (hWherm k ω))
          (fun k _ => measurable_lambdaMax_of_forall (hWmeas k) (hWherm k))
      have heq : (Finset.univ.sup' Finset.univ_nonempty
          (fun k (ω : Ω) => lambdaMax (hWherm k ω))) =
          fun ω => Finset.univ.sup' Finset.univ_nonempty
            (fun k => lambdaMax (hWherm k ω)) := by
        funext ω
        exact Finset.sup'_apply _ _ _
      rw [heq] at hm
      exact hm.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact Finset.sup'_le _ _ fun k _ => hWmax k ω
      · let k0 : I := Classical.arbitrary I
        exact (le_lambdaMin _ fun i => (hWpsd k0 ω).eigenvalues_nonneg i).trans
          ((lambdaMin_le_eigenvalues (hWherm k0 ω)
            (Classical.arbitrary (Fin d₁ ⊕ Fin d₂))).trans
            ((eigenvalues_le_lambdaMax (hWherm k0 ω)
              (Classical.arbitrary (Fin d₁ ⊕ Fin d₂))).trans
              (Finset.le_sup' (fun k => lambdaMax (hWherm k ω))
                (Finset.mem_univ k0))))
  have hsumWherm : ∀ ω, (∑ k, W k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hWherm k ω
  have hsumWbd : ∀ ω, ‖∑ k, W k ω‖ ≤ Csq := by
    intro ω
    calc
      ‖∑ k, W k ω‖ ≤ ∑ k, ‖W k ω‖ := norm_sum_le _ _
      _ = ∑ k, ‖S k ω‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        exact hWnorm k ω
      _ ≤ ∑ k, (R k) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        nlinarith [norm_nonneg (S k ω), h_bdd k ω]
  have hYint : Integrable (fun ω => lambdaMax
      (isHermitian_matsum Finset.univ (fun k => hWherm k ω))) μ :=
    integrable_lambdaMax (measurable_matsum Finset.univ hWmeas)
      hsumWherm hsumWbd
  have hros := matrix_rosenthal_aux (mu := μ) (X := W)
    hWmeas hWherm hWmin hWint hWind hsupint hYint
  have hsumWpsd : ∀ ω, (∑ k, W k ω).PosSemidef := fun ω =>
    posSemidef_matsum Finset.univ fun k => hWpsd k ω
  have hlhs : (fun ω => lambdaMax
      (isHermitian_matsum Finset.univ (fun k => hWherm k ω))) =
      fun ω => max ‖∑ k, S k ω * (S k ω)ᴴ‖
        ‖∑ k, (S k ω)ᴴ * S k ω‖ := by
    funext ω
    rw [← posSemidef_l2_opNorm_eq_lambdaMax (hsumWpsd ω)]
    dsimp only [W]
    simp_rw [pow_two, hermDilation_sq]
    rw [sum_fromBlocks_diagonal, l2_opNorm_fromBlocks_diagonal]
  have hEsumpsd : (∑ k, expectation μ (W k)).PosSemidef := by
    refine posSemidef_matsum Finset.univ fun k => ?_
    exact posSemidef_expectation (hWint k)
      (Filter.Eventually.of_forall fun ω => hWpsd k ω)
  have hvar : lambdaMax (isHermitian_sum_expectation (μ := μ) hWherm) =
      max
        ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
        ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ := by
    rw [← posSemidef_l2_opNorm_eq_lambdaMax hEsumpsd]
    change ‖∑ k, expectation μ (fun ω => (hermDilation (S k ω)) ^ 2)‖ = _
    exact norm_sum_expectation_hermDilation_sq S
  have hmaxpoint : (fun ω => Finset.univ.sup' Finset.univ_nonempty
      (fun k => lambdaMax (hWherm k ω))) =
      fun ω => ⨆ k, ‖S k ω‖ ^ 2 := by
    funext ω
    have hk : ∀ k, lambdaMax (hWherm k ω) = ‖S k ω‖ ^ 2 := by
      intro k
      rw [← posSemidef_l2_opNorm_eq_lambdaMax (hWpsd k ω), hWnorm]
    simp_rw [hk]
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun k _ =>
        le_ciSup (Finite.bddAbove_range fun j => ‖S j ω‖ ^ 2) k
    · exact ciSup_le fun k =>
        Finset.le_sup' (fun j => ‖S j ω‖ ^ 2) (Finset.mem_univ k)
  rw [hlhs, hvar, hmaxpoint] at hros
  rw [Fintype.card_sum] at hros
  simpa only [maxSummandSq, Fintype.card_fin, Nat.cast_add] using hros

/-- Lean implementation helper.

The complete large-dimension squared estimate before final scalar algebra. -/
lemma symmetric_large_squared_bound
    {S : I → Ω → Matrix (Fin d₁) (Fin d₂) ℂ}
    (h_indep : iIndepFun S μ) (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) μ)
    {R : I → ℝ} (h_bdd : ∀ k ω, ‖S k ω‖ ≤ R k)
    (hD : 32 ≤ d₁ + d₂) :
    ∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ ≤
      4 * (1 + Real.log (d₁ + d₂)) *
        max
          ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ +
      16 * Real.exp 1 * Real.log (d₁ + d₂) *
        (1 + Real.log (d₁ + d₂)) * maxSummandSq S μ := by
  let ell : ℝ := Real.log (d₁ + d₂)
  let Q : ℝ := ∫ ω, max ‖∑ k, S k ω * (S k ω)ᴴ‖
    ‖∑ k, (S k ω)ᴴ * S k ω‖ ∂μ
  let V : ℝ := max
    ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
    ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖
  let M : ℝ := maxSummandSq S μ
  have hell : 0 ≤ ell := by
    dsimp only [ell]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ d₁ + d₂ by omega))
  have hfirst : (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ) ≤ 2 * (1 + ell) * Q := by
    simpa only [ell, Q] using
      symmetric_expect_sq_le_square_function h_indep h_meas h_symm h_bdd
  have hsecond : Q ≤ 2 * V + 8 * Real.exp 1 * M * ell := by
    simpa only [Q, V, M, ell] using
      square_function_integral_le_rosenthal h_indep h_meas h_bdd
  calc
    (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂μ) ≤ 2 * (1 + ell) * Q := hfirst
    _ ≤ 2 * (1 + ell) * (2 * V + 8 * Real.exp 1 * M * ell) :=
      mul_le_mul_of_nonneg_left hsecond (by positivity)
    _ = 4 * (1 + Real.log (d₁ + d₂)) *
        max
          ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ +
      16 * Real.exp 1 * Real.log (d₁ + d₂) *
        (1 + Real.log (d₁ + d₂)) * maxSummandSq S μ := by
      dsimp only [ell, V, M]
      ring



end SymmetricLargeDimension


section DimensionConstants

/-- Lean implementation helper. -/
private lemma mul_log_two_le_log_nat {j D : ℕ} (hD : 2 ^ j ≤ D) :
    (j : ℝ) * Real.log 2 ≤ Real.log D := by
  have hpowpos : (0 : ℝ) < 2 ^ j := by positivity
  calc
    (j : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ j) := by
      rw [Real.log_pow]
    _ ≤ Real.log D := Real.log_le_log hpowpos (by exact_mod_cast hD)

/-- Lean implementation helper.

In dimensions below `32`, the Frobenius/variance estimate fits under the
variance term in the exact CGT display. -/
lemma small_dimension_min_le_variance_coefficient {d₁ d₂ : ℕ}
    (hD2 : 2 ≤ d₁ + d₂) (hD32 : d₁ + d₂ < 32) :
    (min d₁ d₂ : ℝ) ≤
      2 * Real.exp 1 * Real.log (d₁ + d₂) := by
  let D := d₁ + d₂
  have hmin : 2 * min d₁ d₂ ≤ D := by
    dsimp only [D]
    omega
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  by_cases h4 : D < 4
  · have hmin1 : min d₁ d₂ ≤ 1 := by omega
    have hlog := mul_log_two_le_log_nat (j := 1) (D := D) (by omega)
    have hlog' : (0.6931471803 : ℝ) ≤ Real.log (d₁ + d₂) :=
      (le_of_lt hl2).trans (by simpa [D] using hlog)
    have hprod : 2 * (2.7182818283 : ℝ) * 0.6931471803 ≤
        2 * Real.exp 1 * Real.log (d₁ + d₂) := by
      gcongr
    have hmin1' : (min d₁ d₂ : ℝ) ≤ 1 := by exact_mod_cast hmin1
    exact hmin1'.trans
      ((by norm_num : (1 : ℝ) ≤ 2 * 2.7182818283 * 0.6931471803).trans hprod)
  by_cases h8 : D < 8
  · have hmin3 : min d₁ d₂ ≤ 3 := by omega
    have hlog := mul_log_two_le_log_nat (j := 2) (D := D) (by omega)
    have hlog' : 2 * (0.6931471803 : ℝ) ≤ Real.log (d₁ + d₂) :=
      (mul_le_mul_of_nonneg_left (le_of_lt hl2) (by norm_num)).trans
        (by simpa [D] using hlog)
    have hprod : 2 * (2.7182818283 : ℝ) * (2 * 0.6931471803) ≤
        2 * Real.exp 1 * Real.log (d₁ + d₂) := by
      gcongr
    have hmin3' : (min d₁ d₂ : ℝ) ≤ 3 := by exact_mod_cast hmin3
    exact hmin3'.trans
      ((by norm_num : (3 : ℝ) ≤ 2 * 2.7182818283 * (2 * 0.6931471803)).trans hprod)
  by_cases h16 : D < 16
  · have hmin7 : min d₁ d₂ ≤ 7 := by omega
    have hlog := mul_log_two_le_log_nat (j := 3) (D := D) (by omega)
    have hlog' : 3 * (0.6931471803 : ℝ) ≤ Real.log (d₁ + d₂) :=
      (mul_le_mul_of_nonneg_left (le_of_lt hl2) (by norm_num)).trans
        (by simpa [D] using hlog)
    have hprod : 2 * (2.7182818283 : ℝ) * (3 * 0.6931471803) ≤
        2 * Real.exp 1 * Real.log (d₁ + d₂) := by
      gcongr
    have hmin7' : (min d₁ d₂ : ℝ) ≤ 7 := by exact_mod_cast hmin7
    exact hmin7'.trans
      ((by norm_num : (7 : ℝ) ≤ 2 * 2.7182818283 * (3 * 0.6931471803)).trans hprod)
  · have hmin15 : min d₁ d₂ ≤ 15 := by omega
    have hlog := mul_log_two_le_log_nat (j := 4) (D := D) (by omega)
    have hlog' : 4 * (0.6931471803 : ℝ) ≤ Real.log (d₁ + d₂) :=
      (mul_le_mul_of_nonneg_left (le_of_lt hl2) (by norm_num)).trans
        (by simpa [D] using hlog)
    have hprod : 2 * (2.7182818283 : ℝ) * (4 * 0.6931471803) ≤
        2 * Real.exp 1 * Real.log (d₁ + d₂) := by
      gcongr
    have hmin15' : (min d₁ d₂ : ℝ) ≤ 15 := by exact_mod_cast hmin15
    exact hmin15'.trans
      ((by norm_num : (15 : ℝ) ≤ 2 * 2.7182818283 * (4 * 0.6931471803)).trans hprod)

/-- Lean implementation helper.

Above dimension `32`, the elementary Rademacher/positive-Rosenthal
coefficients fit under the exact CGT coefficients. -/
lemma large_dimension_rosenthal_coefficients {D : ℕ} (hD : 32 ≤ D) :
    2 * (1 + Real.log D) ≤ Real.exp 1 * Real.log D ∧
      1 + Real.log D ≤ Real.exp 1 * Real.log D := by
  have hDpos : (0 : ℝ) < D := by positivity
  have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have hlog : 5 * Real.log 2 ≤ Real.log D := by
    rw [← hlog32]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hD)
  have hlower : (5 * (0.6931471803 : ℝ)) < Real.log D :=
    lt_of_lt_of_le (by nlinarith [Real.log_two_gt_d9]) hlog
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hprod : 0 ≤
      (Real.exp 1 - 2.7182818283) *
        (Real.log D - 5 * 0.6931471803) := by positivity
  have hfirst : 2 * (1 + Real.log D) ≤ Real.exp 1 * Real.log D := by
    nlinarith
  exact ⟨hfirst, (by
    have hnonneg : 0 ≤ 1 + Real.log D := by
      have : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))
      linarith
    nlinarith)⟩

/-- Lean implementation helper.

Final square-root algebra for the large-dimension symmetric argument. -/
lemma symmetric_large_dimension_algebra
    {y V M ℓ : ℝ} (hy0 : 0 ≤ y) (hV : 0 ≤ V) (hM : 0 ≤ M)
    (hℓ : 0 ≤ ℓ)
    (hc₁ : 2 * (1 + ℓ) ≤ Real.exp 1 * ℓ)
    (hc₂ : 1 + ℓ ≤ Real.exp 1 * ℓ)
    (hy : y ≤ 4 * (1 + ℓ) * V +
      16 * Real.exp 1 * ℓ * (1 + ℓ) * M) :
    y ^ ((1 : ℝ) / 2) ≤
      Real.sqrt (2 * Real.exp 1 * V * ℓ) +
        4 * Real.exp 1 * Real.sqrt M * ℓ := by
  let a := Real.sqrt (2 * Real.exp 1 * V * ℓ)
  let b := 4 * Real.exp 1 * Real.sqrt M * ℓ
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := by positivity
  have hrad : 0 ≤ 2 * Real.exp 1 * V * ℓ := by positivity
  have ha2 : a ^ 2 = 2 * Real.exp 1 * V * ℓ := by
    dsimp only [a]
    exact Real.sq_sqrt hrad
  have hsM : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM
  have hb2 : b ^ 2 =
      16 * (Real.exp 1) ^ 2 * M * ℓ ^ 2 := by
    dsimp only [b]
    rw [mul_pow, mul_pow, mul_pow, hsM]
    ring
  have hfirst : 4 * (1 + ℓ) * V ≤ a ^ 2 := by
    rw [ha2]
    nlinarith
  have hsecond :
      16 * Real.exp 1 * ℓ * (1 + ℓ) * M ≤ b ^ 2 := by
    rw [hb2]
    have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    nlinarith [mul_nonneg (mul_nonneg he0 hℓ) hM]
  have hyab : y ≤ (a + b) ^ 2 := by
    calc
      y ≤ 4 * (1 + ℓ) * V +
          16 * Real.exp 1 * ℓ * (1 + ℓ) * M := hy
      _ ≤ a ^ 2 + b ^ 2 := add_le_add hfirst hsecond
      _ ≤ (a + b) ^ 2 := by nlinarith
  rw [← Real.sqrt_eq_rpow]
  calc
    Real.sqrt y ≤ Real.sqrt ((a + b) ^ 2) := Real.sqrt_le_sqrt hyab
    _ = a + b := Real.sqrt_sq (add_nonneg ha0 hb0)
    _ = _ := rfl

/-- Lean implementation helper.

Final algebra for the low-dimensional Frobenius branch. -/
lemma symmetric_small_dimension_algebra
    {y V M c ℓ : ℝ} (hy0 : 0 ≤ y) (hV : 0 ≤ V) (hM : 0 ≤ M)
    (hℓ : 0 ≤ ℓ) (hy : y ≤ c * V)
    (hc : c ≤ 2 * Real.exp 1 * ℓ) :
    y ^ ((1 : ℝ) / 2) ≤
      Real.sqrt (2 * Real.exp 1 * V * ℓ) +
        4 * Real.exp 1 * Real.sqrt M * ℓ := by
  have hrad : 0 ≤ 2 * Real.exp 1 * V * ℓ := by positivity
  have hy' : y ≤ 2 * Real.exp 1 * V * ℓ :=
    hy.trans (by nlinarith)
  rw [← Real.sqrt_eq_rpow]
  exact (Real.sqrt_le_sqrt hy').trans
    (le_add_of_nonneg_right (by positivity))

end DimensionConstants

section SymmetricTheorem

variable {Omega : Type uOmega} [MeasurableSpace Omega] {mu : Measure Omega}
variable [IsProbabilityMeasure mu]
variable {d1 d2 : Nat} {I : Type uI} [Fintype I] [DecidableEq I]

/-- Lean implementation helper. -/
lemma matrix_rosenthal_pinelis_symmetric_empty_index [IsEmpty I]
    (S : I -> Omega -> Matrix (Fin d1) (Fin d2) Complex) :
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ^ ((1 : Real) / 2) <=
      Real.sqrt (2 * Real.exp 1 *
        (max
          ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
          ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖) *
        Real.log (d1 + d2)) +
      4 * Real.exp 1 * (maxSummandSq S mu) ^ ((1 : Real) / 2) *
        Real.log (d1 + d2) := by
  simp [maxSummandSq]

/-- Lean implementation helper.

Assembly of the exact symmetric Rosenthal--Pinelis conclusion from the stated
large-dimension squared estimate. -/
theorem matrix_rosenthal_pinelis_symmetric_of_large_squared_bound
    {S : I -> Omega -> Matrix (Fin d1) (Fin d2) Complex}
    (hind : iIndepFun S mu) (hmeas : forall k, Measurable (S k))
    (hsymm : forall k, IsSymmetricRV (S k) mu)
    {R : I -> Real} (hbdd : forall k omega, ‖S k omega‖ <= R k)
    (hlarge : 32 <= d1 + d2 ->
      (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) <=
        4 * (1 + Real.log (d1 + d2)) *
          (max
            ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
            ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖) +
        16 * Real.exp 1 * Real.log (d1 + d2) *
          (1 + Real.log (d1 + d2)) * maxSummandSq S mu) :
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ^ ((1 : Real) / 2) <=
      Real.sqrt (2 * Real.exp 1 *
        (max
          ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
          ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖) *
        Real.log (d1 + d2)) +
      4 * Real.exp 1 * (maxSummandSq S mu) ^ ((1 : Real) / 2) *
        Real.log (d1 + d2) := by
  by_cases hd1 : d1 = 0
  · subst d1
    have hS0 : S = fun _ _ => 0 := by
      funext k omega
      ext i
      exact Fin.elim0 i
    rw [hS0]
    simp [maxSummandSq]
  by_cases hd2 : d2 = 0
  · subst d2
    have hS0 : S = fun _ _ => 0 := by
      funext k omega
      ext i j
      exact Fin.elim0 j
    rw [hS0]
    simp [maxSummandSq]
  haveI : Nonempty (Fin d1) := Fintype.card_pos_iff.mp (by simp [Nat.pos_of_ne_zero hd1])
  haveI : Nonempty (Fin d2) := Fintype.card_pos_iff.mp (by simp [Nat.pos_of_ne_zero hd2])
  let y : Real := ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu
  let V : Real := max
    ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
    ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖
  let M : Real := maxSummandSq S mu
  let ell : Real := Real.log (d1 + d2)
  have hy0 : 0 <= y := by
    dsimp only [y]
    exact integral_nonneg fun omega => sq_nonneg _
  have hV0 : 0 <= V := by
    dsimp only [V]
    exact (norm_nonneg _).trans (le_max_left _ _)
  have hM0 : 0 <= M := by
    dsimp only [M]
    exact maxSummandSq_nonneg S
  have hD2 : 2 <= d1 + d2 := by omega
  have hell0 : 0 <= ell := by
    dsimp only [ell]
    exact Real.log_nonneg (by exact_mod_cast (show 1 <= d1 + d2 by omega))
  have hcent : forall k, expectation mu (S k) = 0 := fun k =>
    expectation_eq_zero_of_isSymmetricRV (hmeas k) (hsymm k)
  by_cases hD32 : d1 + d2 < 32
  · have hy : y <= (min d1 d2 : Real) * V := by
      simpa only [y, V, Fintype.card_fin] using
        centered_sum_norm_sq_le_min_card_variance hind hmeas hcent hbdd
    have hc : (min d1 d2 : Real) <= 2 * Real.exp 1 * ell := by
      simpa only [ell] using small_dimension_min_le_variance_coefficient hD2 hD32
    have h := symmetric_small_dimension_algebra hy0 hV0 hM0 hell0 hy hc
    simpa only [y, V, M, ell, Real.sqrt_eq_rpow] using h
  · have hDlarge : 32 <= d1 + d2 := by omega
    have hc := large_dimension_rosenthal_coefficients hDlarge
    have hc' : 2 * (1 + ell) <= Real.exp 1 * ell /\
        1 + ell <= Real.exp 1 * ell := by
      simpa only [ell, Nat.cast_add] using hc
    have hy : y <= 4 * (1 + ell) * V +
        16 * Real.exp 1 * ell * (1 + ell) * M := by
      simpa only [y, V, M, ell] using hlarge hDlarge
    have h := symmetric_large_dimension_algebra hy0 hV0 hM0 hell0 hc'.1 hc'.2 hy
    simpa only [y, V, M, ell, Real.sqrt_eq_rpow] using h



/-- Lean implementation helper.

The exact `q = 2` rectangular consequence of [CGT12a, Theorem A.1(2)]
under its substantive distributional-symmetry hypothesis.  Hermitian dilation
introduces no loss in either coefficient.

Author note: these coefficients agree exactly with Book display (6.1.6), but
the proved theorem assumes distributional symmetry, as does the cited CGT
result. The literal centered/exact Book display is not asserted here. -/
theorem matrix_rosenthal_pinelis_symmetric_aux
    {S : I → Omega → Matrix (Fin d1) (Fin d2) ℂ}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) mu)
    {R : I → ℝ} (h_bdd : ∀ k ω, ‖S k ω‖ ≤ R k) :
    (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂mu) ^ ((1 : ℝ) / 2) ≤
      Real.sqrt (2 * Real.exp 1 *
        (max ‖∑ k, expectation mu (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation mu (fun ω => (S k ω)ᴴ * S k ω)‖) *
        Real.log (d1 + d2)) +
      4 * Real.exp 1 * (maxSummandSq S mu) ^ ((1 : ℝ) / 2) *
        Real.log (d1 + d2) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
      letI := hI
      exact matrix_rosenthal_pinelis_symmetric_empty_index S
  | inr hI =>
      letI := hI
      by_cases hd1 : d1 = 0
      · subst d1
        have hS0 : S = fun _ _ => 0 := by
          funext k ω
          ext i
          exact Fin.elim0 i
        rw [hS0]
        simp [maxSummandSq]
      by_cases hd2 : d2 = 0
      · subst d2
        have hS0 : S = fun _ _ => 0 := by
          funext k ω
          ext i j
          exact Fin.elim0 j
        rw [hS0]
        simp [maxSummandSq]
      haveI : Nonempty (Fin d1) :=
        Fintype.card_pos_iff.mp (by simp [Nat.pos_of_ne_zero hd1])
      haveI : Nonempty (Fin d2) :=
        Fintype.card_pos_iff.mp (by simp [Nat.pos_of_ne_zero hd2])
      apply matrix_rosenthal_pinelis_symmetric_of_large_squared_bound
        h_indep h_meas h_symm h_bdd
      intro hD
      exact symmetric_large_squared_bound h_indep h_meas h_symm h_bdd hD

end SymmetricTheorem

section CenteredLossTheorem

variable {Omega : Type uOmega} [MeasurableSpace Omega] {mu : Measure Omega}
variable [IsProbabilityMeasure mu]
variable {d1 d2 : Nat} {I : Type uI} [Fintype I] [DecidableEq I]

/-- Lean implementation helper.

For merely centered summands, independent-copy symmetrization incurs a
factor `sqrt 2` in the variance coefficient and a factor `2` in the maximum
summand coefficient.

Author note: compared with Book display (6.1.6), the proved centered theorem
has respective coefficient losses `sqrt 2` and `2`; no optimality claim is
made, and the literal centered/exact display is not asserted. -/
theorem matrix_rosenthal_pinelis_centered_with_loss_aux
    {S : I → Omega → Matrix (Fin d1) (Fin d2) ℂ}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, expectation mu (S k) = 0)
    {R : I → ℝ} (h_bdd : ∀ k ω, ‖S k ω‖ ≤ R k) :
    (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂mu) ^ ((1 : ℝ) / 2) ≤
      Real.sqrt (4 * Real.exp 1 *
        (max ‖∑ k, expectation mu (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation mu (fun ω => (S k ω)ᴴ * S k ω)‖) *
        Real.log (d1 + d2)) +
      8 * Real.exp 1 * (maxSummandSq S mu) ^ ((1 : ℝ) / 2) *
        Real.log (d1 + d2) := by
  classical
  by_cases hd1 : d1 = 0
  · subst d1
    have hS0 : S = fun _ _ => 0 := by
      funext k ω
      ext i
      exact Fin.elim0 i
    rw [hS0]
    simp [maxSummandSq]
  by_cases hd2 : d2 = 0
  · subst d2
    have hS0 : S = fun _ _ => 0 := by
      funext k ω
      ext i j
      exact Fin.elim0 j
    rw [hS0]
    simp [maxSummandSq]
  haveI : Nonempty (Fin d1) :=
    Fintype.card_pos_iff.mp (by simp [Nat.pos_of_ne_zero hd1])
  haveI : Nonempty (Fin d2) :=
    Fintype.card_pos_iff.mp (by simp [Nat.pos_of_ne_zero hd2])
  let Delta : I → (Omega × Omega) → Matrix (Fin d1) (Fin d2) ℂ := ghostDiff S
  have hDmeas : ∀ k, Measurable (Delta k) := fun k => measurable_ghostDiff h_meas k
  have hDind : iIndepFun Delta (mu.prod mu) :=
    iIndepFun_ghostDiff h_indep h_meas
  have hDsymm : ∀ k, IsSymmetricRV (Delta k) (mu.prod mu) := fun k =>
    ghostDiff_symmetric h_meas k
  have hDbd : ∀ k p, ‖Delta k p‖ ≤ 2 * |R k| := by
    intro k p
    dsimp only [Delta, ghostDiff]
    calc
      ‖S k p.1 - S k p.2‖ ≤ ‖S k p.1‖ + ‖S k p.2‖ := norm_sub_le _ _
      _ ≤ R k + R k := add_le_add (h_bdd k p.1) (h_bdd k p.2)
      _ ≤ 2 * |R k| := by nlinarith [le_abs_self (R k)]
  have hsym := matrix_rosenthal_pinelis_symmetric_aux
    (mu := mu.prod mu) hDind hDmeas hDsymm hDbd
  have hghost := ghost_l2_symmetrization h_meas h_cent h_bdd
  have hleft0 : 0 ≤ ∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂mu :=
    integral_nonneg fun _ => sq_nonneg _
  have hleft :
      (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂mu) ^ ((1 : ℝ) / 2) ≤
        (∫ p, ‖∑ k, Delta k p‖ ^ 2 ∂(mu.prod mu)) ^ ((1 : ℝ) / 2) := by
    exact Real.rpow_le_rpow hleft0 (by simpa only [Delta] using hghost) (by norm_num)
  have hvars := fun k => ghostDiff_variances_of_bound h_meas h_cent h_bdd k
  have hrow :
      (∑ k, expectation (mu.prod mu)
        (fun p => Delta k p * (Delta k p)ᴴ)) =
        2 • (∑ k, expectation mu (fun ω => S k ω * (S k ω)ᴴ)) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      simpa only [Delta] using (hvars k).1
  have hcol :
      (∑ k, expectation (mu.prod mu)
        (fun p => (Delta k p)ᴴ * Delta k p)) =
        2 • (∑ k, expectation mu (fun ω => (S k ω)ᴴ * S k ω)) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      simpa only [Delta] using (hvars k).2
  let V : ℝ := max
    ‖∑ k, expectation mu (fun ω => S k ω * (S k ω)ᴴ)‖
    ‖∑ k, expectation mu (fun ω => (S k ω)ᴴ * S k ω)‖
  let M : ℝ := maxSummandSq S mu
  let MD : ℝ := maxSummandSq Delta (mu.prod mu)
  let ell : ℝ := Real.log (d1 + d2)
  have hV0 : 0 ≤ V := by
    dsimp only [V]
    exact (norm_nonneg _).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := by
    dsimp only [M]
    exact maxSummandSq_nonneg S
  have hMD0 : 0 ≤ MD := by
    dsimp only [MD]
    exact maxSummandSq_nonneg Delta
  have hell0 : 0 ≤ ell := by
    dsimp only [ell]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ d1 + d2 by omega))
  have hvarDelta :
      max
        ‖∑ k, expectation (mu.prod mu)
          (fun p => Delta k p * (Delta k p)ᴴ)‖
        ‖∑ k, expectation (mu.prod mu)
          (fun p => (Delta k p)ᴴ * Delta k p)‖ = 2 * V := by
    rw [hrow, hcol]
    simp only [← Nat.cast_smul_eq_nsmul ℂ, norm_smul, Complex.norm_natCast]
    dsimp only [V]
    exact (mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hMD : MD ≤ 4 * M := by
    simpa only [MD, M, Delta] using maxSummandSq_ghostDiff_le h_meas h_bdd
  have hsqrtMD : MD ^ ((1 : ℝ) / 2) ≤ 2 * M ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    calc
      Real.sqrt MD ≤ Real.sqrt (4 * M) := Real.sqrt_le_sqrt hMD
      _ = 2 * Real.sqrt M := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ = _ := by rw [Real.sqrt_eq_rpow]
  have hsym' :
      (∫ p, ‖∑ k, Delta k p‖ ^ 2 ∂(mu.prod mu)) ^ ((1 : ℝ) / 2) ≤
        Real.sqrt (4 * Real.exp 1 * V * ell) +
          4 * Real.exp 1 * MD ^ ((1 : ℝ) / 2) * ell := by
    rw [hvarDelta] at hsym
    have hsym'' :
        (∫ p, ‖∑ k, Delta k p‖ ^ 2 ∂(mu.prod mu)) ^ ((1 : ℝ) / 2) ≤
          Real.sqrt (2 * Real.exp 1 * (2 * V) * ell) +
            4 * Real.exp 1 * MD ^ ((1 : ℝ) / 2) * ell := by
      simpa only [MD, ell] using hsym
    convert hsym'' using 1 <;> ring
  calc
    (∫ ω, ‖∑ k, S k ω‖ ^ 2 ∂mu) ^ ((1 : ℝ) / 2) ≤
        (∫ p, ‖∑ k, Delta k p‖ ^ 2 ∂(mu.prod mu)) ^ ((1 : ℝ) / 2) := hleft
    _ ≤ Real.sqrt (4 * Real.exp 1 * V * ell) +
        4 * Real.exp 1 * MD ^ ((1 : ℝ) / 2) * ell := hsym'
    _ ≤ Real.sqrt (4 * Real.exp 1 * V * ell) +
        8 * Real.exp 1 * M ^ ((1 : ℝ) / 2) * ell := by
      apply add_le_add (le_refl _)
      calc
        4 * Real.exp 1 * MD ^ ((1 : ℝ) / 2) * ell =
            (4 * Real.exp 1 * ell) * MD ^ ((1 : ℝ) / 2) := by ring
        _ ≤ (4 * Real.exp 1 * ell) * (2 * M ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hsqrtMD (by positivity)
        _ = 8 * Real.exp 1 * M ^ ((1 : ℝ) / 2) * ell := by ring
    _ = _ := by rfl

end CenteredLossTheorem

section IntegrableRosenthalPinelis

variable {Omega : Type uOmega} [MeasurableSpace Omega] {mu : Measure Omega}
variable [IsProbabilityMeasure mu]
variable {d1 d2 : Nat} {I : Type uI} [Fintype I] [DecidableEq I]

/-! These helpers isolate the only analytic change from the bounded proofs:
for a finite family, every squared norm, every squared signed sum, and both
matrix square functions are dominated by a fixed finite multiple of
`sup_k ‖S_k‖²`. -/

/-- Lean implementation helper. -/
lemma integrable_norm_sq_sum_of_integrable_max [Nonempty I]
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_meas : ∀ k, Measurable (S k))
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    Integrable (fun omega => ‖∑ k, S k omega‖ ^ 2) mu := by
  let Q : Omega → Real := fun omega => ⨆ k, ‖S k omega‖ ^ 2
  have hsum_meas : Measurable (fun omega => ∑ k, S k omega) :=
    Finset.measurable_sum Finset.univ fun k _ => h_meas k
  refine (hM.const_mul ((Fintype.card I : Real) ^ 2)).mono'
    ((continuous_l2_opNorm.measurable.comp hsum_meas).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnorm : ‖∑ k, S k omega‖ ≤ ∑ k, ‖S k omega‖ := norm_sum_le _ _
  have hsquares : (∑ k, ‖S k omega‖) ^ 2 ≤
      (Fintype.card I : Real) * ∑ k, ‖S k omega‖ ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset I)) (f := fun k => ‖S k omega‖))
  have hterms : (∑ k, ‖S k omega‖ ^ 2) ≤
      (Fintype.card I : Real) * Q omega := by
    calc
      (∑ k, ‖S k omega‖ ^ 2) ≤ ∑ _k : I, Q omega := by
        exact Finset.sum_le_sum fun k _ =>
          le_ciSup (Finite.bddAbove_range fun j => ‖S j omega‖ ^ 2) k
      _ = (Fintype.card I : Real) * Q omega := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum0 : 0 ≤ ∑ k, ‖S k omega‖ :=
    Finset.sum_nonneg fun k (_ : k ∈ (Finset.univ : Finset I)) =>
      norm_nonneg (S k omega)
  have hsq : ‖∑ k, S k omega‖ ^ 2 ≤ (∑ k, ‖S k omega‖) ^ 2 := by
    nlinarith [norm_nonneg (∑ k, S k omega)]
  calc
    ‖∑ k, S k omega‖ ^ 2 ≤ (∑ k, ‖S k omega‖) ^ 2 := hsq
    _ ≤ (Fintype.card I : Real) * ∑ k, ‖S k omega‖ ^ 2 := hsquares
    _ ≤ (Fintype.card I : Real) *
        ((Fintype.card I : Real) * (⨆ k, ‖S k omega‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hterms (Nat.cast_nonneg _)
    _ = (Fintype.card I : Real) ^ 2 * (⨆ k, ‖S k omega‖ ^ 2) := by ring

/-- Lean implementation helper. -/
lemma second_moment_data_of_integrable_max [Nonempty I]
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_meas : ∀ k, Measurable (S k))
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) (k : I) :
    MIntegrable (S k) mu ∧
      MIntegrable (fun omega => S k omega * (S k omega)ᴴ) mu ∧
      MIntegrable (fun omega => (S k omega)ᴴ * S k omega) mu := by
  let Q : Omega → Real := fun omega => ⨆ j, ‖S j omega‖ ^ 2
  have hsk2 : Integrable (fun omega => ‖S k omega‖ ^ 2) mu := by
    refine hM.mono'
      ((continuous_l2_opNorm.measurable.comp (h_meas k)).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_ciSup (Finite.bddAbove_range fun j => ‖S j omega‖ ^ 2) k
  have hSlp : MemLp (S k) 2 mu :=
    (memLp_two_iff_integrable_sq_norm (h_meas k).aestronglyMeasurable).2 hsk2
  have hSint : Integrable (S k) mu := hSlp.integrable (by norm_num)
  have hSentry : MIntegrable (S k) mu := fun i j =>
    hSint.mono (((measurable_entry i j).comp (h_meas k)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega => norm_entry_le_l2_opNorm_rect _ _ _)
  have hrow : MIntegrable (fun omega => S k omega * (S k omega)ᴴ) mu := by
    intro i j
    refine hsk2.mono'
      (((measurable_entry i j).comp
        (measurable_mul_conjTranspose_self (h_meas k))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega => ?_)
    calc
      ‖(S k omega * (S k omega)ᴴ) i j‖ ≤
          ‖S k omega * (S k omega)ᴴ‖ := norm_entry_le_l2_opNorm_rect _ _ _
      _ = ‖S k omega‖ ^ 2 := (l2_opNorm_sq_eq (S k omega)).1.symm
  have hcol : MIntegrable (fun omega => (S k omega)ᴴ * S k omega) mu := by
    intro i j
    refine hsk2.mono'
      (((measurable_entry i j).comp
        (measurable_conjTranspose_mul_self (h_meas k))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega => ?_)
    calc
      ‖((S k omega)ᴴ * S k omega) i j‖ ≤
          ‖(S k omega)ᴴ * S k omega‖ := norm_entry_le_l2_opNorm_rect _ _ _
      _ = ‖S k omega‖ ^ 2 := (l2_opNorm_sq_eq (S k omega)).2.symm
  exact ⟨hSentry, hrow, hcol⟩

/-- Lean implementation helper. -/
lemma integrable_square_function_of_integrable_max [Nonempty I]
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_meas : ∀ k, Measurable (S k))
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    Integrable (fun omega => max
      ‖∑ k, S k omega * (S k omega)ᴴ‖
      ‖∑ k, (S k omega)ᴴ * S k omega‖) mu := by
  let Q : Omega → Real := fun omega => ⨆ k, ‖S k omega‖ ^ 2
  have hm : Measurable (fun omega => max
      ‖∑ k, S k omega * (S k omega)ᴴ‖
      ‖∑ k, (S k omega)ᴴ * S k omega‖) := by
    exact (continuous_l2_opNorm.measurable.comp
      (Finset.measurable_sum Finset.univ fun k _ =>
        measurable_mul_conjTranspose_self (h_meas k))).max
      (continuous_l2_opNorm.measurable.comp
        (Finset.measurable_sum Finset.univ fun k _ =>
          measurable_conjTranspose_mul_self (h_meas k)))
  refine (hM.const_mul (Fintype.card I : Real)).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    ((norm_nonneg _).trans (le_max_left _ _))]
  apply max_le
  · calc
      ‖∑ k, S k omega * (S k omega)ᴴ‖ ≤
          ∑ k, ‖S k omega * (S k omega)ᴴ‖ := norm_sum_le _ _
      _ = ∑ k, ‖S k omega‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        exact (l2_opNorm_sq_eq (S k omega)).1.symm
      _ ≤ ∑ _k : I, Q omega := Finset.sum_le_sum fun k _ =>
        le_ciSup (Finite.bddAbove_range fun j => ‖S j omega‖ ^ 2) k
      _ = (Fintype.card I : Real) * Q omega := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · -- the second diagonal block is identical
    calc
      ‖∑ k, (S k omega)ᴴ * S k omega‖ ≤
          ∑ k, ‖(S k omega)ᴴ * S k omega‖ := norm_sum_le _ _
      _ = ∑ k, ‖S k omega‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        exact (l2_opNorm_sq_eq (S k omega)).2.symm
      _ ≤ ∑ _k : I, Q omega := Finset.sum_le_sum fun k _ =>
        le_ciSup (Finite.bddAbove_range fun j => ‖S j omega‖ ^ 2) k
      _ = (Fintype.card I : Real) * Q omega := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Lean implementation helper: the sign-reflection/Rademacher step with no
boundedness assumption. -/
lemma symmetric_expect_sq_le_square_function_integrable [Nonempty I]
    [Nonempty (Fin d1)] [Nonempty (Fin d2)]
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) mu)
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu ≤
      2 * (1 + Real.log (d1 + d2)) *
        ∫ omega, max ‖∑ k, S k omega * (S k omega)ᴴ‖
          ‖∑ k, (S k omega)ᴴ * S k omega‖ ∂mu := by
  classical
  let qsign : (I → Bool) → Omega → Real := fun b omega =>
    ‖∑ k, boolSign (b k) • S k omega‖ ^ 2
  let vsq : Omega → Real := fun omega =>
    max ‖∑ k, S k omega * (S k omega)ᴴ‖
      ‖∑ k, (S k omega)ᴴ * S k omega‖
  have hsign_meas : ∀ b : I → Bool, ∀ k,
      Measurable (fun omega => boolSign (b k) • S k omega) := by
    intro b k
    exact measurable_const.smul (h_meas k)
  have hqsign_int : ∀ b, Integrable (qsign b) mu := by
    intro b
    let T : I → Omega → Matrix (Fin d1) (Fin d2) Complex :=
      fun k omega => boolSign (b k) • S k omega
    have hTM : Integrable (fun omega => ⨆ k, ‖T k omega‖ ^ 2) mu := by
      refine hM.congr (Filter.Eventually.of_forall fun omega => ?_)
      have hk : ∀ k, ‖T k omega‖ ^ 2 = ‖S k omega‖ ^ 2 := by
        intro k
        by_cases hb : b k = true <;> simp [T, boolSign, hb]
      simp_rw [hk]
    simpa only [qsign, T] using
      integrable_norm_sq_sum_of_integrable_max (fun k => hsign_meas b k) hTM
  have hleft_int : Integrable
      (fun omega => (Fintype.card (I → Bool) : Real)⁻¹ *
        ∑ b : I → Bool, qsign b omega) mu :=
    (integrable_finsetSum Finset.univ fun b _ => hqsign_int b).const_mul _
  have hvsq_int : Integrable vsq mu := by
    simpa only [vsq] using
      integrable_square_function_of_integrable_max h_meas hM
  have hpoint : ∀ omega,
      (Fintype.card (I → Bool) : Real)⁻¹ *
          ∑ b : I → Bool, qsign b omega ≤
        2 * (1 + Real.log (d1 + d2)) * vsq omega := by
    intro omega
    have hr := bool_rademacher_rect_expect_sq_upper
      (A := fun k => S k omega)
    have hintb : Integrable (fun b : I → Bool =>
        ‖∑ k, boolSign (b k) • S k omega‖ ^ 2)
        (Measure.pi fun _ : I => boolRademacherMeasure) := Integrable.of_finite
    have havg :
        (∫ b : I → Bool, ‖∑ k, boolSign (b k) • S k omega‖ ^ 2
          ∂Measure.pi fun _ : I => boolRademacherMeasure) =
          (Fintype.card (I → Bool) : Real)⁻¹ *
            ∑ b : I → Bool, qsign b omega := by
      rw [integral_fintype hintb]
      simp_rw [boolRademacher_pi_singleton]
      simp only [smul_eq_mul, Finset.mul_sum, qsign]
    rw [havg] at hr
    dsimp only [vsq]
    nlinarith
  have hint := integral_mono hleft_int
    (hvsq_int.const_mul (2 * (1 + Real.log (d1 + d2)))) hpoint
  have hreflect : ∀ b : I → Bool,
      (∫ omega, qsign b omega ∂mu) =
        ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu := by
    intro b
    simpa only [qsign, signFlip, boolSign, ite_smul, one_smul, neg_one_smul] using
      integral_signFlip_eq_of_symmetric h_indep h_meas h_symm b
        (measurable_matrix_family_sum_norm_sq
          (I := I) (d₁ := d1) (d₂ := d2))
  rw [integral_const_mul,
    integral_finsetSum Finset.univ (fun b _ => hqsign_int b)] at hint
  simp_rw [hreflect] at hint
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hint
  rw [integral_const_mul] at hint
  have hcard : (Fintype.card (I → Bool) : Real) ≠ 0 := by positivity
  simpa [vsq, inv_mul_cancel₀ hcard] using hint

/-- Lean implementation helper: the positive-matrix Rosenthal step under a
finite expected maximum squared norm. -/
lemma square_function_integral_le_rosenthal_integrable [Nonempty I]
    [Nonempty (Fin d1)] [Nonempty (Fin d2)]
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    (∫ omega, max ‖∑ k, S k omega * (S k omega)ᴴ‖
        ‖∑ k, (S k omega)ᴴ * S k omega‖ ∂mu) ≤
      2 * max
        ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
        ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ +
      8 * Real.exp 1 * maxSummandSq S mu * Real.log (d1 + d2) := by
  classical
  let W : I → Omega → Matrix (Fin d1 ⊕ Fin d2) (Fin d1 ⊕ Fin d2) Complex :=
    fun k omega => (hermDilation (S k omega)) ^ 2
  have hWmeas : ∀ k, Measurable (W k) := by
    intro k
    dsimp only [W]
    simpa only [pow_two, Function.comp_apply] using measurable_matrix_mul_local
      (measurable_hermDilation_fun.comp (h_meas k))
      (measurable_hermDilation_fun.comp (h_meas k))
  have hWpsd : ∀ k omega, (W k omega).PosSemidef := fun k omega => by
    dsimp only [W]
    rw [pow_two]
    exact posSemidef_sq (isHermitian_hermDilation (S k omega))
  have hWherm : ∀ k omega, (W k omega).IsHermitian :=
    fun k omega => (hWpsd k omega).1
  have hWmin : ∀ k omega, 0 ≤ lambdaMin (hWherm k omega) :=
    fun k omega => le_lambdaMin _ fun i => (hWpsd k omega).eigenvalues_nonneg i
  have hWnorm : ∀ k omega, ‖W k omega‖ = ‖S k omega‖ ^ 2 := by
    intro k omega
    dsimp only [W]
    rw [pow_two]
    have heq : hermDilation (S k omega) * hermDilation (S k omega) =
        (hermDilation (S k omega))ᴴ * hermDilation (S k omega) := by
      rw [(isHermitian_hermDilation (S k omega)).eq]
    rw [heq, ← (l2_opNorm_sq_eq (hermDilation (S k omega))).2,
      l2_opNorm_hermDilation]
  have hsk2 : ∀ k, Integrable (fun omega => ‖S k omega‖ ^ 2) mu := by
    intro k
    refine hM.mono'
      ((continuous_l2_opNorm.measurable.comp (h_meas k)).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_ciSup (Finite.bddAbove_range fun j => ‖S j omega‖ ^ 2) k
  have hWint : ∀ k, MIntegrable (W k) mu := by
    intro k i j
    refine (hsk2 k).mono'
      (((measurable_entry i j).comp (hWmeas k)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega => ?_)
    exact (norm_entry_le_l2_opNorm _ _ _).trans_eq (hWnorm k omega)
  have hmap : Measurable (fun A : Matrix (Fin d1) (Fin d2) Complex =>
      (hermDilation A) ^ 2) := by
    rw [show (fun A : Matrix (Fin d1) (Fin d2) Complex => (hermDilation A) ^ 2) =
      fun A => hermDilation A * hermDilation A by funext A; rw [pow_two]]
    exact measurable_matrix_mul_local measurable_hermDilation_fun measurable_hermDilation_fun
  have hWind : iIndepFun W mu :=
    h_indep.comp (fun _ A => (hermDilation A) ^ 2) (fun _ => hmap)
  have hsumWpsd : ∀ omega, (∑ k, W k omega).PosSemidef := fun omega =>
    posSemidef_matsum Finset.univ fun k => hWpsd k omega
  have hsumWherm : ∀ omega, (∑ k, W k omega).IsHermitian :=
    fun omega => (hsumWpsd omega).1
  have hsup_eq : (fun omega => Finset.univ.sup' Finset.univ_nonempty
      (fun k => lambdaMax (hWherm k omega))) =
      fun omega => ⨆ k, ‖S k omega‖ ^ 2 := by
    funext omega
    have hk : ∀ k, lambdaMax (hWherm k omega) = ‖S k omega‖ ^ 2 := by
      intro k
      rw [← posSemidef_l2_opNorm_eq_lambdaMax (hWpsd k omega), hWnorm]
    simp_rw [hk]
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun k _ =>
        le_ciSup (Finite.bddAbove_range fun j => ‖S j omega‖ ^ 2) k
    · exact ciSup_le fun k =>
        Finset.le_sup' (fun j => ‖S j omega‖ ^ 2) (Finset.mem_univ k)
  have hsupint : Integrable (fun omega => Finset.univ.sup' Finset.univ_nonempty
      (fun k => lambdaMax (hWherm k omega))) mu := by rw [hsup_eq]; exact hM
  have hlhs : (fun omega => lambdaMax
      (isHermitian_matsum Finset.univ (fun k => hWherm k omega))) =
      fun omega => max ‖∑ k, S k omega * (S k omega)ᴴ‖
        ‖∑ k, (S k omega)ᴴ * S k omega‖ := by
    funext omega
    rw [← posSemidef_l2_opNorm_eq_lambdaMax (hsumWpsd omega)]
    dsimp only [W]
    simp_rw [pow_two, hermDilation_sq]
    rw [sum_fromBlocks_diagonal, l2_opNorm_fromBlocks_diagonal]
  have hYint : Integrable (fun omega => lambdaMax
      (isHermitian_matsum Finset.univ (fun k => hWherm k omega))) mu := by
    rw [hlhs]
    exact integrable_square_function_of_integrable_max h_meas hM
  have hros := matrix_rosenthal_aux (mu := mu) (X := W)
    hWmeas hWherm hWmin hWint hWind hsupint hYint
  have hEsumpsd : (∑ k, expectation mu (W k)).PosSemidef := by
    refine posSemidef_matsum Finset.univ fun k => ?_
    exact posSemidef_expectation (hWint k)
      (Filter.Eventually.of_forall fun omega => hWpsd k omega)
  have hvar : lambdaMax (isHermitian_sum_expectation (μ := mu) hWherm) =
      max
        ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
        ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ := by
    rw [← posSemidef_l2_opNorm_eq_lambdaMax hEsumpsd]
    change ‖∑ k, expectation mu (fun omega => (hermDilation (S k omega)) ^ 2)‖ = _
    exact norm_sum_expectation_hermDilation_sq S
  rw [hlhs, hvar, hsup_eq] at hros
  rw [Fintype.card_sum] at hros
  simpa only [maxSummandSq, Fintype.card_fin, Nat.cast_add] using hros

/-- Lean implementation helper: low-dimensional Frobenius estimate under the
finite expected maximum-square hypothesis. -/
lemma centered_sum_norm_sq_le_card_row_variance_integrable [Nonempty I]
    [Nonempty (Fin d1)]
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, expectation mu (S k) = 0)
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ≤
      (d1 : Real) *
        ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖ := by
  let Z : Omega → Matrix (Fin d1) (Fin d2) Complex := fun omega => ∑ k, S k omega
  have hdata := fun k => second_moment_data_of_integrable_max h_meas hM k
  have hS : ∀ k, MIntegrable (S k) mu := fun k => (hdata k).1
  have hS1 : ∀ k, MIntegrable
      (fun omega => S k omega * (S k omega)ᴴ) mu := fun k => (hdata k).2.1
  have hZmeas : Measurable Z :=
    Finset.measurable_sum Finset.univ fun k _ => h_meas k
  have hZsq : Integrable (fun omega => ‖Z omega‖ ^ 2) mu := by
    simpa only [Z] using integrable_norm_sq_sum_of_integrable_max h_meas hM
  have hZgram : MIntegrable (fun omega => Z omega * (Z omega)ᴴ) mu := by
    intro i j
    refine (hM.const_mul ((Fintype.card I : Real) ^ 2)).mono'
      (((measurable_entry i j).comp
        (measurable_mul_conjTranspose_self hZmeas)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega => ?_)
    calc
      ‖(Z omega * (Z omega)ᴴ) i j‖ ≤ ‖Z omega * (Z omega)ᴴ‖ :=
        norm_entry_le_l2_opNorm_rect _ _ _
      _ = ‖Z omega‖ ^ 2 := (l2_opNorm_sq_eq (Z omega)).1.symm
      _ ≤ (Fintype.card I : Real) ^ 2 * (⨆ k, ‖S k omega‖ ^ 2) := by
        have hnorm : ‖Z omega‖ ≤ ∑ k, ‖S k omega‖ := norm_sum_le _ _
        have hsquares : (∑ k, ‖S k omega‖) ^ 2 ≤
            (Fintype.card I : Real) * ∑ k, ‖S k omega‖ ^ 2 := by
          simpa using (sq_sum_le_card_mul_sum_sq
            (s := (Finset.univ : Finset I)) (f := fun k => ‖S k omega‖))
        have hsum0 : 0 ≤ ∑ k, ‖S k omega‖ :=
          Finset.sum_nonneg fun k (_ : k ∈ (Finset.univ : Finset I)) =>
            norm_nonneg (S k omega)
        have hsq : ‖Z omega‖ ^ 2 ≤ (∑ k, ‖S k omega‖) ^ 2 := by
          nlinarith [norm_nonneg (Z omega)]
        have hterms : (∑ k, ‖S k omega‖ ^ 2) ≤
            (Fintype.card I : Real) * (⨆ k, ‖S k omega‖ ^ 2) := by
          calc
            (∑ k, ‖S k omega‖ ^ 2) ≤
                ∑ _k : I, (⨆ j, ‖S j omega‖ ^ 2) :=
              Finset.sum_le_sum fun k _ =>
                le_ciSup (Finite.bddAbove_range fun j => ‖S j omega‖ ^ 2) k
            _ = (Fintype.card I : Real) * (⨆ k, ‖S k omega‖ ^ 2) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        calc
          ‖Z omega‖ ^ 2 ≤ (∑ k, ‖S k omega‖) ^ 2 := hsq
          _ ≤ (Fintype.card I : Real) * ∑ k, ‖S k omega‖ ^ 2 := hsquares
          _ ≤ (Fintype.card I : Real) *
              ((Fintype.card I : Real) * (⨆ k, ‖S k omega‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hterms (Nat.cast_nonneg _)
          _ = _ := by ring
  have htraceint : Integrable
      (fun omega => (Z omega * (Z omega)ᴴ).trace) mu :=
    integrable_finsetSum Finset.univ fun i _ => hZgram i i
  have hfrobint : Integrable (fun omega => frobeniusNorm (Z omega) ^ 2) mu := by
    refine htraceint.re.congr (Filter.Eventually.of_forall fun omega => ?_)
    change ((Z omega * (Z omega)ᴴ).trace).re = frobeniusNorm (Z omega) ^ 2
    rw [trace_mul_conjTranspose_self]
    exact Complex.ofReal_re _
  have hfrob_eq :
      (∫ omega, frobeniusNorm (Z omega) ^ 2 ∂mu) =
        ((expectation mu fun omega => Z omega * (Z omega)ᴴ).trace).re := by
    have htr := congrArg Complex.re (expectation_trace hZgram)
    calc
      (∫ omega, frobeniusNorm (Z omega) ^ 2 ∂mu) =
          ∫ omega, ((Z omega * (Z omega)ᴴ).trace).re ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with omega
        rw [trace_mul_conjTranspose_self]
        exact (Complex.ofReal_re _).symm
      _ = (∫ omega, (Z omega * (Z omega)ᴴ).trace ∂mu).re :=
        integral_re htraceint
      _ = ((expectation mu fun omega => Z omega * (Z omega)ᴴ).trace).re := htr
  have hEgram : expectation mu (fun omega => Z omega * (Z omega)ᴴ) =
      ∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ) := by
    simpa only [Z] using
      expectation_sum_mul_conjTranspose_of_centered h_indep h_meas hS hS1 h_cent
  let A : Matrix (Fin d1) (Fin d1) Complex :=
    ∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)
  have hApsd : A.PosSemidef :=
    posSemidef_matsum Finset.univ fun k =>
      posSemidef_expectation (hS1 k)
        (Filter.Eventually.of_forall fun omega =>
          Matrix.posSemidef_self_mul_conjTranspose (S k omega))
  calc
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) =
        ∫ omega, ‖Z omega‖ ^ 2 ∂mu := by rfl
    _ ≤ ∫ omega, frobeniusNorm (Z omega) ^ 2 ∂mu :=
      integral_mono hZsq hfrobint fun omega => by
        nlinarith [l2_opNorm_le_frobeniusNorm (Z omega), norm_nonneg (Z omega),
          frobeniusNorm_nonneg (Z omega)]
    _ = A.trace.re := by rw [hfrob_eq, hEgram]
    _ ≤ (Fintype.card (Fin d1) : Real) * ‖A‖ :=
      trace_re_le_card_mul_l2_opNorm_of_posSemidef hApsd
    _ = _ := by simp [A]

/-- Lean implementation helper. -/
lemma centered_sum_norm_sq_le_min_card_variance_integrable [Nonempty I]
    [Nonempty (Fin d1)] [Nonempty (Fin d2)]
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, expectation mu (S k) = 0)
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ≤
      (min d1 d2 : Real) * max
        ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
        ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ := by
  have hrow := centered_sum_norm_sq_le_card_row_variance_integrable
    h_indep h_meas h_cent hM
  let T : I → Omega → Matrix (Fin d2) (Fin d1) Complex :=
    fun k omega => (S k omega)ᴴ
  have hTind : iIndepFun T mu :=
    h_indep.comp (fun _ A => Aᴴ) (fun _ => measurable_conjTranspose_map)
  have hTmeas : ∀ k, Measurable (T k) := fun k =>
    measurable_conjTranspose_map.comp (h_meas k)
  have hTcent : ∀ k, expectation mu (T k) = 0 := by
    intro k
    dsimp only [T]
    rw [expectation_conjTranspose, h_cent k, Matrix.conjTranspose_zero]
  have hTM : Integrable (fun omega => ⨆ k, ‖T k omega‖ ^ 2) mu := by
    simpa only [T, Matrix.l2_opNorm_conjTranspose] using hM
  have hcolT := centered_sum_norm_sq_le_card_row_variance_integrable
    hTind hTmeas hTcent hTM
  have hcol : (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ≤
      (d2 : Real) *
        ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ := by
    simpa only [T, ← Matrix.conjTranspose_sum, Matrix.l2_opNorm_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using hcolT
  by_cases hle : d1 ≤ d2
  · calc
      (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ≤
          (d1 : Real) *
            ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖ := hrow
      _ ≤ (d1 : Real) * max
          ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
          ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)
      _ = _ := by rw [min_eq_left (by exact_mod_cast hle : (d1 : Real) ≤ d2)]
  · have hle' : d2 ≤ d1 := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    calc
      (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ≤
          (d2 : Real) *
            ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ := hcol
      _ ≤ (d2 : Real) * max
          ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
          ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _)
      _ = _ := by rw [min_eq_right (by exact_mod_cast hle' : (d2 : Real) ≤ d1)]

/-- Lean implementation helper: large-dimension squared estimate under the
finite expected maximum-square hypothesis. -/
lemma symmetric_large_squared_bound_integrable [Nonempty I]
    [Nonempty (Fin d1)] [Nonempty (Fin d2)]
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) mu)
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu ≤
      4 * (1 + Real.log (d1 + d2)) *
        max
          ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
          ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖ +
      16 * Real.exp 1 * Real.log (d1 + d2) *
        (1 + Real.log (d1 + d2)) * maxSummandSq S mu := by
  let ell : Real := Real.log (d1 + d2)
  let Q : Real := ∫ omega, max ‖∑ k, S k omega * (S k omega)ᴴ‖
    ‖∑ k, (S k omega)ᴴ * S k omega‖ ∂mu
  let V : Real := max
    ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
    ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖
  let M : Real := maxSummandSq S mu
  have hfirst : (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ≤
      2 * (1 + ell) * Q := by
    simpa only [ell, Q] using
      symmetric_expect_sq_le_square_function_integrable
        h_indep h_meas h_symm hM
  have hsecond : Q ≤ 2 * V + 8 * Real.exp 1 * M * ell := by
    simpa only [Q, V, M, ell] using
      square_function_integral_le_rosenthal_integrable h_indep h_meas hM
  have hell : 0 ≤ ell := by
    dsimp only [ell]
    have hd1pos : 0 < d1 := Fin.pos_iff_nonempty.mpr inferInstance
    have hd2pos : 0 < d2 := Fin.pos_iff_nonempty.mpr inferInstance
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ d1 + d2 by omega))
  calc
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ≤ 2 * (1 + ell) * Q := hfirst
    _ ≤ 2 * (1 + ell) * (2 * V + 8 * Real.exp 1 * M * ell) :=
      mul_le_mul_of_nonneg_left hsecond (by positivity)
    _ = _ := by dsimp only [ell, V, M]; ring

/-- The exact-coefficient symmetric form of **Book display (6.1.6)** under
its natural finite-heavy-tail assumption.  This removes the boundedness
convenience assumption from `matrix_rosenthal_pinelis_symmetric_aux`. -/
theorem matrix_rosenthal_pinelis_symmetric_integrable_aux
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) mu)
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ^ ((1 : Real) / 2) ≤
      Real.sqrt (2 * Real.exp 1 *
        (max ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
          ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖) *
        Real.log (d1 + d2)) +
      4 * Real.exp 1 * (maxSummandSq S mu) ^ ((1 : Real) / 2) *
        Real.log (d1 + d2) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
      letI := hI
      exact matrix_rosenthal_pinelis_symmetric_empty_index S
  | inr hI =>
      letI := hI
      by_cases hd1 : d1 = 0
      · subst d1
        have hS0 : S = fun _ _ => 0 := by
          funext k omega
          ext i
          exact Fin.elim0 i
        rw [hS0]
        simp [maxSummandSq]
      by_cases hd2 : d2 = 0
      · subst d2
        have hS0 : S = fun _ _ => 0 := by
          funext k omega
          ext i j
          exact Fin.elim0 j
        rw [hS0]
        simp [maxSummandSq]
      haveI : Nonempty (Fin d1) :=
        Fintype.card_pos_iff.mp (by simp [Nat.pos_of_ne_zero hd1])
      haveI : Nonempty (Fin d2) :=
        Fintype.card_pos_iff.mp (by simp [Nat.pos_of_ne_zero hd2])
      let y : Real := ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu
      let V : Real := max
        ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
        ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖
      let M : Real := maxSummandSq S mu
      let ell : Real := Real.log (d1 + d2)
      have hy0 : 0 ≤ y := integral_nonneg fun _ => sq_nonneg _
      have hV0 : 0 ≤ V := (norm_nonneg _).trans (le_max_left _ _)
      have hM0 : 0 ≤ M := maxSummandSq_nonneg S
      have hD2 : 2 ≤ d1 + d2 := by omega
      have hell0 : 0 ≤ ell :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ d1 + d2 by omega))
      have hcent : ∀ k, expectation mu (S k) = 0 := fun k =>
        expectation_eq_zero_of_isSymmetricRV (h_meas k) (h_symm k)
      by_cases hD32 : d1 + d2 < 32
      · have hy : y ≤ (min d1 d2 : Real) * V := by
          simpa only [y, V] using
            centered_sum_norm_sq_le_min_card_variance_integrable
              h_indep h_meas hcent hM
        have hc : (min d1 d2 : Real) ≤ 2 * Real.exp 1 * ell := by
          simpa only [ell] using small_dimension_min_le_variance_coefficient hD2 hD32
        have h := symmetric_small_dimension_algebra hy0 hV0 hM0 hell0 hy hc
        simpa only [y, V, M, ell, Real.sqrt_eq_rpow] using h
      · have hDlarge : 32 ≤ d1 + d2 := by omega
        have hc := large_dimension_rosenthal_coefficients hDlarge
        have hc' : 2 * (1 + ell) ≤ Real.exp 1 * ell ∧
            1 + ell ≤ Real.exp 1 * ell := by
          simpa only [ell, Nat.cast_add] using hc
        have hy : y ≤ 4 * (1 + ell) * V +
            16 * Real.exp 1 * ell * (1 + ell) * M := by
          simpa only [y, V, M, ell] using
            symmetric_large_squared_bound_integrable h_indep h_meas h_symm hM
        have h := symmetric_large_dimension_algebra
          hy0 hV0 hM0 hell0 hc'.1 hc'.2 hy
        simpa only [y, V, M, ell, Real.sqrt_eq_rpow] using h

/-- Lean implementation helper: independent-copy second-moment identities
under a finite expected maximum-square hypothesis. -/
lemma ghostDiff_variances_of_integrable_max [Nonempty I]
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, expectation mu (S k) = 0)
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) (k : I) :
    expectation (mu.prod mu)
        (fun p => ghostDiff S k p * (ghostDiff S k p)ᴴ) =
        2 • expectation mu (fun omega => S k omega * (S k omega)ᴴ) ∧
      expectation (mu.prod mu)
        (fun p => (ghostDiff S k p)ᴴ * ghostDiff S k p) =
        2 • expectation mu (fun omega => (S k omega)ᴴ * S k omega) := by
  have hd := second_moment_data_of_integrable_max h_meas hM k
  constructor
  · simpa only [ghostDiff] using
      (ghostDiff_rowVariance (mu := mu) (S := S k) (h_meas k)
        hd.1 hd.2.1 (h_cent k))
  · simpa only [ghostDiff] using
      (ghostDiff_colVariance (mu := mu) (S := S k) (h_meas k)
        hd.1 hd.2.2 (h_cent k))

/-- Lean implementation helper: ghost-copy symmetrization with only a finite
second moment of the maximum summand. -/
lemma ghost_l2_symmetrization_integrable [Nonempty I]
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, expectation mu (S k) = 0)
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ≤
      ∫ p : Omega × Omega, ‖∑ k, ghostDiff S k p‖ ^ 2 ∂(mu.prod mu) := by
  let Z : Omega → Matrix (Fin d1) (Fin d2) Complex := fun omega => ∑ k, S k omega
  let D : Omega × Omega → Matrix (Fin d1) (Fin d2) Complex :=
    fun p => Z p.1 - Z p.2
  have hZm : Measurable Z := Finset.measurable_sum Finset.univ fun k _ => h_meas k
  have hSint : ∀ k, MIntegrable (S k) mu := fun k =>
    (second_moment_data_of_integrable_max h_meas hM k).1
  have hZint : MIntegrable Z mu := fun i j => by
    simpa only [Z, Matrix.sum_apply] using
      (integrable_finsetSum Finset.univ fun k _ => hSint k i j)
  have hEZ : expectation mu Z = 0 := by
    rw [show expectation mu Z = ∑ k, expectation mu (S k) by
      exact expectation_finsetSum Finset.univ fun k _ => hSint k]
    simp [h_cent]
  have hZsq : Integrable (fun omega => ‖Z omega‖ ^ 2) mu := by
    simpa only [Z] using integrable_norm_sq_sum_of_integrable_max h_meas hM
  have hDm : Measurable D := (hZm.comp measurable_fst).sub (hZm.comp measurable_snd)
  have hDsq : Integrable (fun p => ‖D p‖ ^ 2) (mu.prod mu) := by
    refine ((hZsq.comp_fst mu).const_mul 2 |>.add
      ((hZsq.comp_snd mu).const_mul 2)).mono'
      ((continuous_l2_opNorm.measurable.comp hDm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    change ‖‖D p‖ ^ 2‖ ≤ 2 * ‖Z p.1‖ ^ 2 + 2 * ‖Z p.2‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsub := norm_sub_le (Z p.1) (Z p.2)
    dsimp only [D]
    nlinarith [norm_nonneg (Z p.1), norm_nonneg (Z p.2),
      norm_nonneg (Z p.1 - Z p.2), sq_nonneg (‖Z p.1‖ - ‖Z p.2‖)]
  have hpoint : ∀ omega, ‖Z omega‖ ^ 2 ≤
      ∫ omega', ‖D (omega, omega')‖ ^ 2 ∂mu := by
    intro omega
    let V : Omega → Matrix (Fin d1) (Fin d2) Complex :=
      fun omega' => Z omega - Z omega'
    have hVm : Measurable V := measurable_const.sub hZm
    have hVint : MIntegrable V mu := (MIntegrable.const (Z omega)).sub hZint
    have hEV : expectation mu V = Z omega := by
      rw [show V = fun omega' => Z omega - Z omega' from rfl,
        expectation_sub (MIntegrable.const _) hZint,
        expectation_const, hEZ, sub_zero]
    have hVsq : Integrable (fun omega' => ‖V omega'‖ ^ 2) mu := by
      refine ((integrable_const (2 * ‖Z omega‖ ^ 2)).add
        (hZsq.const_mul 2)).mono'
        ((continuous_l2_opNorm.measurable.comp hVm).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun omega' => ?_)
      change ‖‖V omega'‖ ^ 2‖ ≤
        2 * ‖Z omega‖ ^ 2 + 2 * ‖Z omega'‖ ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hsub := norm_sub_le (Z omega) (Z omega')
      dsimp only [V]
      nlinarith [norm_nonneg (Z omega), norm_nonneg (Z omega'),
        norm_nonneg (Z omega - Z omega'), sq_nonneg (‖Z omega‖ - ‖Z omega'‖)]
    have hVLp : MemLp V 2 mu :=
      (memLp_two_iff_integrable_sq_norm hVm.aestronglyMeasurable).2 hVsq
    have hVnorm : Integrable (fun omega' => ‖V omega'‖) mu :=
      (hVLp.integrable (by norm_num)).norm
    have hj := norm_expectation_le hVint hVnorm
    rw [hEV] at hj
    have hc := integral_sqrt_mul_le_sqrt_integral_mul
      (mu := mu) (M := fun _ : Omega => 1) (Y := fun omega' => ‖V omega'‖ ^ 2)
      (integrable_const 1) hVsq (fun _ => by norm_num) (fun _ => sq_nonneg _)
    simp only [one_mul, Real.sqrt_sq (norm_nonneg _), integral_const,
      probReal_univ, one_smul, one_mul] at hc
    have hinner0 : 0 ≤ ∫ omega', ‖V omega'‖ ^ 2 ∂mu :=
      integral_nonneg fun _ => sq_nonneg _
    have hsqrtSq := Real.sq_sqrt hinner0
    change ‖Z omega‖ ^ 2 ≤ ∫ omega', ‖V omega'‖ ^ 2 ∂mu
    nlinarith [norm_nonneg (Z omega),
      Real.sqrt_nonneg (∫ omega', ‖V omega'‖ ^ 2 ∂mu)]
  have hi := integral_mono hZsq hDsq.integral_prod_left hpoint
  rw [← MeasureTheory.integral_prod _ hDsq] at hi
  simpa only [Z, D, ghostDiff, Finset.sum_sub_distrib] using hi

/-- Lean implementation helper. -/
lemma maxSummandSq_ghostDiff_le_integrable [Nonempty I]
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_meas : ∀ k, Measurable (S k))
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    maxSummandSq (ghostDiff S) (mu.prod mu) ≤ 4 * maxSummandSq S mu := by
  let Q : Omega → Real := fun omega => ⨆ k, ‖S k omega‖ ^ 2
  let QD : Omega × Omega → Real := fun p => ⨆ k, ‖ghostDiff S k p‖ ^ 2
  have hQ0 : ∀ omega, 0 ≤ Q omega := fun omega =>
    (sq_nonneg ‖S (Classical.arbitrary I) omega‖).trans
      (le_ciSup (Finite.bddAbove_range fun k => ‖S k omega‖ ^ 2)
        (Classical.arbitrary I))
  have hQDm : Measurable QD := Measurable.iSup fun k =>
    (continuous_l2_opNorm.measurable.comp (measurable_ghostDiff h_meas k)).pow_const 2
  have hQD0 : ∀ p, 0 ≤ QD p := fun p =>
    (sq_nonneg ‖ghostDiff S (Classical.arbitrary I) p‖).trans
      (le_ciSup (Finite.bddAbove_range fun k => ‖ghostDiff S k p‖ ^ 2)
        (Classical.arbitrary I))
  have hpoint : ∀ p, QD p ≤ 2 * Q p.1 + 2 * Q p.2 := by
    intro p
    apply ciSup_le
    intro k
    have hk1 : ‖S k p.1‖ ^ 2 ≤ Q p.1 :=
      le_ciSup (Finite.bddAbove_range fun j => ‖S j p.1‖ ^ 2) k
    have hk2 : ‖S k p.2‖ ^ 2 ≤ Q p.2 :=
      le_ciSup (Finite.bddAbove_range fun j => ‖S j p.2‖ ^ 2) k
    have hsub := norm_sub_le (S k p.1) (S k p.2)
    change ‖S k p.1 - S k p.2‖ ^ 2 ≤ _
    nlinarith [norm_nonneg (S k p.1), norm_nonneg (S k p.2),
      norm_nonneg (S k p.1 - S k p.2), sq_nonneg (‖S k p.1‖ - ‖S k p.2‖)]
  have hQDint : Integrable QD (mu.prod mu) := by
    have hQint : Integrable Q mu := by simpa only [Q] using hM
    refine ((hQint.comp_fst mu).const_mul 2 |>.add
      ((hQint.comp_snd mu).const_mul 2)).mono' hQDm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    change ‖QD p‖ ≤ 2 * Q p.1 + 2 * Q p.2
    rw [Real.norm_eq_abs, abs_of_nonneg (hQD0 p)]
    exact hpoint p
  have hQint : Integrable Q mu := by simpa only [Q] using hM
  have hRint : Integrable (fun p : Omega × Omega =>
      2 * Q p.1 + 2 * Q p.2) (mu.prod mu) :=
    (hQint.comp_fst mu |>.const_mul 2).add (hQint.comp_snd mu |>.const_mul 2)
  have hi := integral_mono hQDint hRint hpoint
  have hfst : (∫ p : Omega × Omega, Q p.1 ∂(mu.prod mu)) = ∫ omega, Q omega ∂mu := by
    rw [MeasureTheory.integral_prod _ (hQint.comp_fst mu)]
    simp
  have hsnd : (∫ p : Omega × Omega, Q p.2 ∂(mu.prod mu)) = ∫ omega, Q omega ∂mu := by
    rw [MeasureTheory.integral_prod _ (hQint.comp_snd mu)]
    simp
  rw [integral_add (hQint.comp_fst mu |>.const_mul 2)
    (hQint.comp_snd mu |>.const_mul 2), integral_const_mul, integral_const_mul,
    hfst, hsnd] at hi
  dsimp only [Q, QD] at hi
  calc
    maxSummandSq (ghostDiff S) (mu.prod mu) ≤
        2 * maxSummandSq S mu + 2 * maxSummandSq S mu := by
      simpa only [maxSummandSq] using hi
    _ = 4 * maxSummandSq S mu := by ring

/-- The centered finite-heavy-tail counterpart of **Book display (6.1.6)**.
It has the same `sqrt 2` and `2` symmetrization losses as the bounded centered
variant; the literal centered/exact source display is not asserted. -/
theorem matrix_rosenthal_pinelis_centered_with_loss_integrable_aux
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, expectation mu (S k) = 0)
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ^ ((1 : Real) / 2) ≤
      Real.sqrt (4 * Real.exp 1 *
        (max ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
          ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖) *
        Real.log (d1 + d2)) +
      8 * Real.exp 1 * (maxSummandSq S mu) ^ ((1 : Real) / 2) *
        Real.log (d1 + d2) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
      letI := hI
      simp [maxSummandSq]
  | inr hI =>
      letI := hI
      by_cases hd1 : d1 = 0
      · subst d1
        have hS0 : S = fun _ _ => 0 := by
          funext k omega
          ext i
          exact Fin.elim0 i
        rw [hS0]
        simp [maxSummandSq]
      by_cases hd2 : d2 = 0
      · subst d2
        have hS0 : S = fun _ _ => 0 := by
          funext k omega
          ext i j
          exact Fin.elim0 j
        rw [hS0]
        simp [maxSummandSq]
      haveI : Nonempty (Fin d1) :=
        Fintype.card_pos_iff.mp (by simp [Nat.pos_of_ne_zero hd1])
      haveI : Nonempty (Fin d2) :=
        Fintype.card_pos_iff.mp (by simp [Nat.pos_of_ne_zero hd2])
      let Delta : I → (Omega × Omega) → Matrix (Fin d1) (Fin d2) Complex :=
        ghostDiff S
      have hDmeas : ∀ k, Measurable (Delta k) := fun k =>
        measurable_ghostDiff h_meas k
      have hDind : iIndepFun Delta (mu.prod mu) :=
        iIndepFun_ghostDiff h_indep h_meas
      have hDsymm : ∀ k, IsSymmetricRV (Delta k) (mu.prod mu) := fun k =>
        ghostDiff_symmetric h_meas k
      have hDM : Integrable (fun p => ⨆ k, ‖Delta k p‖ ^ 2) (mu.prod mu) := by
        let Q : Omega → Real := fun omega => ⨆ k, ‖S k omega‖ ^ 2
        let QD : Omega × Omega → Real := fun p => ⨆ k, ‖Delta k p‖ ^ 2
        have hQDm : Measurable QD := Measurable.iSup fun k =>
          (continuous_l2_opNorm.measurable.comp (hDmeas k)).pow_const 2
        have hQD0 : ∀ p, 0 ≤ QD p := fun p =>
          (sq_nonneg ‖Delta (Classical.arbitrary I) p‖).trans
            (le_ciSup (Finite.bddAbove_range fun k => ‖Delta k p‖ ^ 2)
              (Classical.arbitrary I))
        have hpoint : ∀ p, QD p ≤ 2 * Q p.1 + 2 * Q p.2 := by
          intro p
          apply ciSup_le
          intro k
          have hk1 : ‖S k p.1‖ ^ 2 ≤ Q p.1 :=
            le_ciSup (Finite.bddAbove_range fun j => ‖S j p.1‖ ^ 2) k
          have hk2 : ‖S k p.2‖ ^ 2 ≤ Q p.2 :=
            le_ciSup (Finite.bddAbove_range fun j => ‖S j p.2‖ ^ 2) k
          have hsub := norm_sub_le (S k p.1) (S k p.2)
          change ‖S k p.1 - S k p.2‖ ^ 2 ≤ _
          nlinarith [norm_nonneg (S k p.1), norm_nonneg (S k p.2),
            norm_nonneg (S k p.1 - S k p.2),
            sq_nonneg (‖S k p.1‖ - ‖S k p.2‖)]
        refine ((hM.comp_fst mu).const_mul 2 |>.add
          ((hM.comp_snd mu).const_mul 2)).mono' hQDm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun p => ?_)
        change ‖QD p‖ ≤ 2 * Q p.1 + 2 * Q p.2
        rw [Real.norm_eq_abs, abs_of_nonneg (hQD0 p)]
        exact hpoint p
      have hsym := matrix_rosenthal_pinelis_symmetric_integrable_aux
        (mu := mu.prod mu) hDind hDmeas hDsymm hDM
      have hghost := ghost_l2_symmetrization_integrable h_meas h_cent hM
      have hleft0 : 0 ≤ ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu :=
        integral_nonneg fun _ => sq_nonneg _
      have hleft :
          (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ^ ((1 : Real) / 2) ≤
            (∫ p, ‖∑ k, Delta k p‖ ^ 2 ∂(mu.prod mu)) ^
              ((1 : Real) / 2) :=
        Real.rpow_le_rpow hleft0 (by simpa only [Delta] using hghost) (by norm_num)
      have hvars := fun k => ghostDiff_variances_of_integrable_max
        h_meas h_cent hM k
      have hrow :
          (∑ k, expectation (mu.prod mu)
            (fun p => Delta k p * (Delta k p)ᴴ)) =
            2 • (∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => by
          simpa only [Delta] using (hvars k).1
      have hcol :
          (∑ k, expectation (mu.prod mu)
            (fun p => (Delta k p)ᴴ * Delta k p)) =
            2 • (∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => by
          simpa only [Delta] using (hvars k).2
      let V : Real := max
        ‖∑ k, expectation mu (fun omega => S k omega * (S k omega)ᴴ)‖
        ‖∑ k, expectation mu (fun omega => (S k omega)ᴴ * S k omega)‖
      let M : Real := maxSummandSq S mu
      let MD : Real := maxSummandSq Delta (mu.prod mu)
      let ell : Real := Real.log (d1 + d2)
      have hM0 : 0 ≤ M := maxSummandSq_nonneg S
      have hMD0 : 0 ≤ MD := maxSummandSq_nonneg Delta
      have hell0 : 0 ≤ ell :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ d1 + d2 by omega))
      have hvarDelta : max
          ‖∑ k, expectation (mu.prod mu)
            (fun p => Delta k p * (Delta k p)ᴴ)‖
          ‖∑ k, expectation (mu.prod mu)
            (fun p => (Delta k p)ᴴ * Delta k p)‖ = 2 * V := by
        rw [hrow, hcol]
        simp only [← Nat.cast_smul_eq_nsmul Complex, norm_smul, Complex.norm_natCast]
        dsimp only [V]
        exact (mul_max_of_nonneg _ _ (by norm_num : (0 : Real) ≤ 2)).symm
      have hMD : MD ≤ 4 * M := by
        simpa only [MD, M, Delta] using
          maxSummandSq_ghostDiff_le_integrable h_meas hM
      have hsqrtMD : MD ^ ((1 : Real) / 2) ≤
          2 * M ^ ((1 : Real) / 2) := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        calc
          Real.sqrt MD ≤ Real.sqrt (4 * M) := Real.sqrt_le_sqrt hMD
          _ = 2 * Real.sqrt M := by
            rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 4)]
            rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hsym' :
          (∫ p, ‖∑ k, Delta k p‖ ^ 2 ∂(mu.prod mu)) ^ ((1 : Real) / 2) ≤
            Real.sqrt (4 * Real.exp 1 * V * ell) +
              4 * Real.exp 1 * MD ^ ((1 : Real) / 2) * ell := by
        rw [hvarDelta] at hsym
        dsimp only [ell, MD] at hsym ⊢
        convert hsym using 1 <;> ring
      calc
        (∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu) ^ ((1 : Real) / 2) ≤
            (∫ p, ‖∑ k, Delta k p‖ ^ 2 ∂(mu.prod mu)) ^
              ((1 : Real) / 2) := hleft
        _ ≤ Real.sqrt (4 * Real.exp 1 * V * ell) +
            4 * Real.exp 1 * MD ^ ((1 : Real) / 2) * ell := hsym'
        _ ≤ Real.sqrt (4 * Real.exp 1 * V * ell) +
            8 * Real.exp 1 * M ^ ((1 : Real) / 2) * ell := by
          apply add_le_add (le_refl _)
          calc
            4 * Real.exp 1 * MD ^ ((1 : Real) / 2) * ell =
                (4 * Real.exp 1 * ell) * MD ^ ((1 : Real) / 2) := by ring
            _ ≤ (4 * Real.exp 1 * ell) * (2 * M ^ ((1 : Real) / 2)) :=
              mul_le_mul_of_nonneg_left hsqrtMD (by positivity)
            _ = _ := by ring
        _ = _ := by rfl

end IntegrableRosenthalPinelis

end

end MatrixConcentration
