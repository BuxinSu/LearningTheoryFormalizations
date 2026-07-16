import MatrixConcentration.Chapter8_ProofOfLiebsTheorem

/-!
# Appendix: Golden–Thompson inequality

This module proves **Book equation (3.3.3)** through the following components.

This consolidated appendix contains:

* trace Cauchy–Schwarz and Schatten-norm estimates;
* Dyson-word expansions and the disentangling inequality;
* the Lie product formula and the Golden–Thompson inequality.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# Appendix A.1: Trace Cauchy–Schwarz (Frobenius pairing)

Supporting toolkit for the appendix proof of the Golden–Thompson
inequality: the Cauchy–Schwarz inequality for the
Frobenius pairing `⟨M, N⟩ = tr(Mᴴ N)`, expressed through the existing
Prelude vector toolkit (`norm_dotProduct_le` on the vectorizations), and
basic reality/positivity facts for traces of psd matrices.

Reference for the appendix development: J. R. Lee, *CSE 599I: Analysis of
Boolean functions* (Spring 2021), Lecture 3 "Golden–Thompson and the
Frobenius inner product" (following Dyson's disentangling argument), and
the classical sources Golden (1965), Thompson (1965).
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Lean implementation helper.

Vectorization of a matrix (row-major), for routing the Frobenius
pairing through the Prelude dot-product toolkit. -/
def mvec (M : Matrix n n ℂ) : n × n → ℂ := fun p => M p.1 p.2

/-- Lean implementation helper.

The Frobenius pairing as a dot product of vectorizations. -/
lemma trace_conjTranspose_mul_eq_dot (M N : Matrix n n ℂ) :
    (Mᴴ * N).trace = star (mvec M) ⬝ᵥ mvec N := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, mvec, Pi.star_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Lean implementation helper.

The squared Frobenius norm as a real sum of squared entry norms. -/
lemma frobSq_eq (M : Matrix n n ℂ) :
    ((Mᴴ * M).trace).re = ∑ p : n × n, ‖M p.1 p.2‖ ^ 2 := by
  rw [trace_conjTranspose_mul_eq_dot, dotProduct]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.star_apply, mvec, RCLike.star_def]
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    show ‖M p.1 p.2‖ ^ 2 = Complex.normSq (M p.1 p.2) from
      (Complex.normSq_eq_norm_sq _).symm, Complex.normSq_apply]
  ring

/-- Lean implementation helper.

`l2norm` of the vectorization is the Frobenius norm. -/
lemma l2norm_mvec (M : Matrix n n ℂ) :
    l2norm (mvec M) = Real.sqrt (((Mᴴ * M).trace).re) := by
  rw [l2norm_eq_sqrt_sum, frobSq_eq]
  rfl

/-- Lean implementation helper.

**Trace Cauchy–Schwarz** (the Frobenius-pairing Cauchy–Schwarz used
throughout the appendix):
`‖tr(Q·R)‖ ≤ √(tr(QᴴQ).re) · √(tr(RᴴR).re)`. -/
theorem trace_mul_le_frob (Q R : Matrix n n ℂ) :
    ‖(Q * R).trace‖ ≤
      Real.sqrt (((Qᴴ * Q).trace).re) * Real.sqrt (((Rᴴ * R).trace).re) := by
  have h1 : (Q * R).trace = star (mvec Qᴴ) ⬝ᵥ mvec R := by
    rw [← trace_conjTranspose_mul_eq_dot, Matrix.conjTranspose_conjTranspose]
  have h2 := norm_dotProduct_le (mvec Qᴴ) (mvec R)
  rw [h1]
  calc ‖star (mvec Qᴴ) ⬝ᵥ mvec R‖ ≤ l2norm (mvec Qᴴ) * l2norm (mvec R) := h2
    _ = Real.sqrt ((((Qᴴ)ᴴ * Qᴴ).trace).re) *
        Real.sqrt (((Rᴴ * R).trace).re) := by rw [l2norm_mvec, l2norm_mvec]
    _ = Real.sqrt (((Qᴴ * Q).trace).re) *
        Real.sqrt (((Rᴴ * R).trace).re) := by
        rw [Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]

/-- Lean implementation helper.

The trace of a psd matrix has nonnegative real part. -/
lemma trace_re_nonneg_of_posSemidef {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    0 ≤ (M.trace).re := by
  have h1 := hM.trace_nonneg
  exact (Complex.le_def.mp h1).1

/-- Lean implementation helper.

The trace of a psd matrix is real: its norm equals its real part. -/
lemma norm_trace_of_posSemidef {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    ‖M.trace‖ = (M.trace).re := by
  have h1 := hM.trace_nonneg
  obtain ⟨hre, him⟩ := Complex.le_def.mp h1
  have h2 : M.trace = ((M.trace).re : ℂ) := by
    refine Complex.ext rfl ?_
    simp only [Complex.ofReal_im]
    exact him.symm
  rw [h2, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
    abs_of_nonneg (by simpa using hre)]

/-- Lean implementation helper.

`tr((XY)^m) = tr((YX)^m)` (cyclic invariance of traces of powers). -/
lemma trace_pow_mul_comm (X Y : Matrix n n ℂ) (m : ℕ) :
    ((X * Y) ^ m).trace = ((Y * X) ^ m).trace := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have h1 : (X * Y) ^ m = X * ((Y * X) ^ (m - 1) * Y) := by
      induction m with
      | zero => omega
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk
          simp [pow_succ]
        · rw [pow_succ, ih hk]
          have h2 : k + 1 - 1 = (k - 1) + 1 := by omega
          rw [h2, pow_succ]
          noncomm_ring
    rw [h1, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]
    have h4 : m - 1 + 1 = m := by omega
    rw [h4]

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Appendix A.2: Dyson's disentangling lemma

The combinatorial heart of the appendix proof of Golden–Thompson
.  For a matrix `A`, a *word* is a product whose
letters are `A` or `Aᴴ`.  **Dyson's lemma** (Dyson 1964; presented in
J. R. Lee, CSE 599I Lecture 3, Lemma 1.3) states that among all words of
length `2m`, the trace is maximized (in absolute value) by the fully
alternating word: `‖tr(A₁A₂⋯A_{2m})‖ ≤ tr((AᴴA)^m)`.

The proof is a finite maximization argument: take a word maximizing
`‖tr‖` with the largest number of *cyclic transitions* (adjacent pairs of
distinct letters).  If it is not fully alternating, rotate an equal
adjacent pair to the midpoint junction, split `P = QR`, and apply the
trace Cauchy–Schwarz: `‖tr(QR)‖² ≤ tr(QᴴQ)·tr(RᴴR)`.  Both `QᴴQ` and
`RᴴR` are again words, with strictly more transitions on average —
contradicting maximality.

From Dyson's lemma the **disentangling chain** (Lee, Lemma 1.2) follows:
`‖tr((UV)^{2^k})‖ ≤ tr(U^{2^k} V^{2^k}).re` for Hermitian `U`, `V`.

Words are represented as `Fin (m + m) → Bool` for the finite
maximization, with all computations performed on `List Bool` via
`List.ofFn` (transition counts are defined recursively on lists, which
keeps the counting lemmas inductive).
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Dyson

/-! ## Letters, words, and their products -/

/-- Lean implementation helper.

The letter of a word: `false ↦ A`, `true ↦ Aᴴ`. -/
noncomputable def ltr (A : Matrix n n ℂ) (b : Bool) : Matrix n n ℂ :=
  cond b Aᴴ A

/-- Lean implementation helper. -/
@[simp] lemma ltr_false (A : Matrix n n ℂ) : ltr A false = A := rfl

/-- Lean implementation helper. -/
@[simp] lemma ltr_true (A : Matrix n n ℂ) : ltr A true = Aᴴ := rfl

/-- Lean implementation helper. -/
lemma ltr_not (A : Matrix n n ℂ) (b : Bool) : ltr A (!b) = (ltr A b)ᴴ := by
  cases b <;> simp

/-- Lean implementation helper.

The matrix product of a `Bool` word. -/
noncomputable def lprod (A : Matrix n n ℂ) (l : List Bool) : Matrix n n ℂ :=
  (l.map (ltr A)).prod

/-- Lean implementation helper. -/
lemma lprod_nil (A : Matrix n n ℂ) : lprod A [] = 1 := rfl

/-- Lean implementation helper. -/
lemma lprod_cons (A : Matrix n n ℂ) (b : Bool) (l : List Bool) :
    lprod A (b :: l) = ltr A b * lprod A l := by
  simp [lprod]

/-- Lean implementation helper. -/
lemma lprod_append (A : Matrix n n ℂ) (l₁ l₂ : List Bool) :
    lprod A (l₁ ++ l₂) = lprod A l₁ * lprod A l₂ := by
  simp [lprod]

/-- Lean implementation helper.

Star of a word product: the reversed, letter-flipped word. -/
lemma lprod_star (A : Matrix n n ℂ) (l : List Bool) :
    (lprod A l)ᴴ = lprod A (l.reverse.map (! ·)) := by
  induction l with
  | nil => simp [lprod]
  | cons b t ih =>
    rw [lprod_cons, Matrix.conjTranspose_mul, ih]
    rw [List.reverse_cons, List.map_append, lprod_append]
    simp [lprod, ltr_not]

/-- Lean implementation helper.

Rotation invariance of the trace of a word product. -/
lemma trace_lprod_rotate (A : Matrix n n ℂ) (l : List Bool) (r : ℕ) :
    (lprod A (l.rotate r)).trace = (lprod A l).trace := by
  rcases Nat.eq_zero_or_pos l.length with hlen | hlen
  · rw [List.length_eq_zero_iff] at hlen
    subst hlen
    simp [List.rotate]
  rw [← List.rotate_mod]
  have hr : r % l.length ≤ l.length := le_of_lt (Nat.mod_lt _ hlen)
  rw [List.rotate_eq_drop_append_take hr, lprod_append,
    Matrix.trace_mul_comm, ← lprod_append, List.take_append_drop]

/-! ## Transition counts on `Bool` lists -/

/-- Lean implementation helper.

The indicator of a transition between two letters. -/
def dd (a b : Bool) : ℕ := if a ≠ b then 1 else 0

/-- Lean implementation helper. -/
lemma dd_comm (a b : Bool) : dd a b = dd b a := by
  cases a <;> cases b <;> rfl

/-- Lean implementation helper. -/
lemma dd_not_not (a b : Bool) : dd (!a) (!b) = dd a b := by
  cases a <;> cases b <;> rfl

/-- Lean implementation helper. -/
lemma dd_not_self (a : Bool) : dd (!a) a = 1 := by
  cases a <;> rfl

/-- Lean implementation helper. -/
lemma dd_le_one (a b : Bool) : dd a b ≤ 1 := by
  cases a <;> cases b <;> simp [dd]

/-- Lean implementation helper.

Linear (non-cyclic) transition count of a `Bool` list. -/
def dtrans : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => dd a b + dtrans (b :: t)

/-- Lean implementation helper.

Cyclic transition count: the linear count plus the wrap-around pair. -/
def ctrans (l : List Bool) : ℕ :=
  dtrans l + (if h : 2 ≤ l.length then
    dd (l.getLast (by intro h'; subst h'; simp at h))
      (l.head (by intro h'; subst h'; simp at h)) else 0)

/-- Lean implementation helper. -/
lemma dtrans_lt_length {l : List Bool} (hl : l ≠ []) :
    dtrans l < l.length := by
  induction l with
  | nil => simp at hl
  | cons a t ih =>
    cases t with
    | nil => simp [dtrans]
    | cons b t' =>
      have h1 := ih (by simp)
      have h2 : dtrans (a :: b :: t') = dd a b + dtrans (b :: t') := rfl
      have h3 := dd_le_one a b
      simp only [List.length_cons] at h1 ⊢
      omega

/-- Lean implementation helper. -/
lemma ctrans_le_length (l : List Bool) : ctrans l ≤ l.length := by
  cases l with
  | nil => simp [ctrans, dtrans]
  | cons a t =>
    rw [ctrans]
    split_ifs with h2
    · have h1 := dtrans_lt_length (l := a :: t) (by simp)
      have h3 := dd_le_one ((a :: t).getLast (by simp))
        ((a :: t).head (by simp))
      omega
    · have h1 := dtrans_lt_length (l := a :: t) (by simp)
      omega

/-- Lean implementation helper.

Appending lists adds the junction transition. -/
lemma dtrans_append (l₁ l₂ : List Bool) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    dtrans (l₁ ++ l₂) =
      dtrans l₁ + dtrans l₂ + dd (l₁.getLast h₁) (l₂.head h₂) := by
  induction l₁ with
  | nil => simp at h₁
  | cons a t ih =>
    cases t with
    | nil =>
      cases l₂ with
      | nil => simp at h₂
      | cons c t₂ =>
        show dd a c + dtrans (c :: t₂) = 0 + dtrans (c :: t₂) + dd a c
        omega
    | cons b t' =>
      have h3 : (a :: b :: t') ++ l₂ = a :: ((b :: t') ++ l₂) := rfl
      rw [h3]
      show dd a b + dtrans ((b :: t') ++ l₂) = _
      rw [ih (by simp)]
      show dd a b + (dtrans (b :: t') + dtrans l₂ +
        dd ((b :: t').getLast (by simp)) (l₂.head h₂)) =
        (dd a b + dtrans (b :: t')) + dtrans l₂ +
          dd ((a :: b :: t').getLast (by simp)) (l₂.head h₂)
      rw [List.getLast_cons_cons]
      omega

/-- Lean implementation helper. -/
lemma dtrans_reverse (l : List Bool) : dtrans l.reverse = dtrans l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t' =>
      rw [List.reverse_cons,
        dtrans_append _ _ (by simp) (by simp), ih]
      show dtrans (b :: t') + 0 +
        dd ((b :: t').reverse.getLast (by simp)) a = dd a b + dtrans (b :: t')
      rw [List.getLast_reverse]
      show dtrans (b :: t') + 0 + dd b a = dd a b + dtrans (b :: t')
      rw [dd_comm]
      omega

/-- Lean implementation helper. -/
lemma dtrans_map_not (l : List Bool) : dtrans (l.map (! ·)) = dtrans l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t' =>
      show dd (!a) (!b) + dtrans ((b :: t').map (! ·)) = dd a b + _
      rw [dd_not_not, ih]

/-- Lean implementation helper. -/
lemma dtrans_le_ctrans (l : List Bool) : dtrans l ≤ ctrans l := by
  rw [ctrans]
  split_ifs <;> omega

/-- Lean implementation helper. -/
lemma ctrans_le_dtrans_add_one (l : List Bool) :
    ctrans l ≤ dtrans l + 1 := by
  rw [ctrans]
  split_ifs with h
  · have := dd_le_one (l.getLast (by intro h'; subst h'; simp at h))
      (l.head (by intro h'; subst h'; simp at h))
    omega
  · omega

/-- Lean implementation helper.

Cyclic transition counts are rotation invariant. -/
lemma ctrans_rotate_one (l : List Bool) : ctrans (l.rotate 1) = ctrans l := by
  match l with
  | [] => rfl
  | [a] => rw [List.rotate_singleton]
  | a :: b :: t =>
    have hrot : (a :: b :: t).rotate 1 = (b :: t) ++ [a] := by
      rw [List.rotate_eq_drop_append_take (by simp)]
      simp
    rw [hrot]
    have h2 : 2 ≤ ((b :: t) ++ [a] : List Bool).length := by simp
    have h2' : 2 ≤ (a :: b :: t : List Bool).length := by simp
    rw [ctrans, dif_pos h2, ctrans, dif_pos h2']
    rw [dtrans_append _ _ (by simp) (by simp)]
    have e1 : ((b :: t) ++ [a] : List Bool).getLast (by simp) = a := by
      rw [List.getLast_eq_getElem]
      simp
    have e2 : ((b :: t) ++ [a] : List Bool).head (by simp) = b := rfl
    have e3 : (a :: b :: t : List Bool).getLast (by simp) =
        (b :: t).getLast (by simp) := by
      rw [List.getLast_eq_getElem, List.getLast_eq_getElem]
      simp
    have e4 : (a :: b :: t : List Bool).head (by simp) = a := rfl
    rw [e1, e2, e3, e4]
    show dtrans (b :: t) + 0 + dd ((b :: t).getLast (by simp)) a + dd a b =
      dd a b + dtrans (b :: t) + dd ((b :: t).getLast (by simp)) a
    omega

/-- Lean implementation helper. -/
lemma ctrans_rotate (l : List Bool) (r : ℕ) :
    ctrans (l.rotate r) = ctrans l := by
  induction r with
  | zero => rw [List.rotate_zero]
  | succ j ih =>
    have h1 : l.rotate (j + 1) = (l.rotate j).rotate 1 := by
      rw [List.rotate_rotate]
    rw [h1, ctrans_rotate_one, ih]

/-! ## The count of the star-word `Qᴴ·Q` and of a split -/

/-- Lean implementation helper.

The word of `QᴴQ` has exactly `2·dtrans Q + 2` cyclic transitions. -/
lemma ctrans_starword (Q : List Bool) (hQ : Q ≠ []) :
    ctrans ((Q.reverse.map (! ·)) ++ Q) = 2 * dtrans Q + 2 := by
  have hrevne : Q.reverse.map (! ·) ≠ [] := by simp [hQ]
  have hQpos : 0 < Q.length := List.length_pos_of_ne_nil hQ
  have h2 : 2 ≤ ((Q.reverse.map (! ·)) ++ Q).length := by
    simp only [List.length_append, List.length_map, List.length_reverse]
    omega
  rw [ctrans, dif_pos h2, dtrans_append _ _ hrevne hQ, dtrans_map_not,
    dtrans_reverse]
  have e1 : ((Q.reverse.map (! ·)) : List Bool).getLast hrevne =
      !(Q.head hQ) := by
    have hidx : Q.length - 1 - (Q.length - 1) = 0 := by omega
    rw [List.getLast_eq_getElem, List.head_eq_getElem_zero hQ]
    simp only [List.length_map, List.length_reverse, List.getElem_map,
      List.getElem_reverse, hidx]
  have e2 : (((Q.reverse.map (! ·)) ++ Q : List Bool)).getLast
      (by simp [hQ]) = Q.getLast hQ := by
    rw [List.getLast_eq_getElem, List.getLast_eq_getElem]
    rw [List.getElem_append_right
      (by simp only [List.length_map, List.length_reverse,
        List.length_append]; omega)]
    have hidx : ((Q.reverse.map (! ·)) ++ Q).length - 1 -
        (Q.reverse.map (! ·)).length = Q.length - 1 := by
      simp only [List.length_map, List.length_reverse, List.length_append]
      omega
    simp only [hidx]
  have e3 : (((Q.reverse.map (! ·)) ++ Q : List Bool)).head
      (by simp [hQ]) = !(Q.getLast hQ) := by
    rw [List.head_eq_getElem_zero (by simp [hQ]), List.getLast_eq_getElem]
    rw [List.getElem_append_left
      (by simp only [List.length_map, List.length_reverse]; omega)]
    simp only [List.getElem_map, List.getElem_reverse, List.length_map,
      List.length_reverse, Nat.sub_zero]
  rw [e1, e2, e3, dd_not_self, dd_comm, dd_not_self]
  omega

/-- Lean implementation helper.

Splitting at an equal junction: the cyclic count of `Q ++ R` is at
most `dtrans Q + dtrans R + 1`. -/
lemma ctrans_split_le (Q R : List Bool) (hQ : Q ≠ []) (hR : R ≠ [])
    (hjunc : Q.getLast hQ = R.head hR) :
    ctrans (Q ++ R) ≤ dtrans Q + dtrans R + 1 := by
  have h1 := ctrans_le_dtrans_add_one (Q ++ R)
  rw [dtrans_append _ _ hQ hR, hjunc] at h1
  have hd0 : dd (R.head hR) (R.head hR) = 0 := by simp [dd]
  omega

/-! ## Alternating words -/

/-- Lean implementation helper.

The alternating `Bool` list starting with `a`. -/
def altL (a : Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 => a :: altL (!a) k

/-- Lean implementation helper. -/
lemma altL_two_step (a : Bool) (k : ℕ) :
    altL a (k + 2) = a :: (!a) :: altL a k := by
  show a :: altL (!a) (k + 1) = a :: (!a) :: altL a k
  show a :: ((!a) :: altL (!(!a)) k) = a :: (!a) :: altL a k
  rw [Bool.not_not]

/-- Lean implementation helper.

A list with maximal linear transition count is alternating. -/
lemma eq_altL_of_dtrans_max :
    ∀ (l : List Bool) (hl : l ≠ []), dtrans l + 1 = l.length →
      l = altL (l.head hl) l.length := by
  intro l
  induction l with
  | nil => intro hl; simp at hl
  | cons a t ih =>
    intro _ h
    cases t with
    | nil => rfl
    | cons b t' =>
      have h1 := dtrans_lt_length (l := b :: t') (by simp)
      have h2 : dtrans (a :: b :: t') = dd a b + dtrans (b :: t') := rfl
      have hdd := dd_le_one a b
      have h3 : dd a b = 1 := by
        simp only [List.length_cons] at h h1
        omega
      have h4 : dtrans (b :: t') + 1 = (b :: t').length := by
        simp only [List.length_cons] at h h1 ⊢
        omega
      have h5 : b = !a := by
        cases a <;> cases b <;> simp [dd] at h3 ⊢
      have h6 := ih (by simp) h4
      rw [show ((b :: t').head (by simp)) = b from rfl] at h6
      subst h5
      have h7 : t' = altL a t'.length := by
        rw [show ((!a) :: t' : List Bool).length = t'.length + 1 from rfl,
          show altL (!a) (t'.length + 1) =
            (!a) :: altL (!(!a)) t'.length from rfl, Bool.not_not] at h6
        injection h6
      show a :: (!a) :: t' = altL a (t'.length + 1 + 1)
      rw [show t'.length + 1 + 1 = t'.length + 2 from rfl, altL_two_step,
        ← h7]

/-- Lean implementation helper.

The word product of the alternating list of even length. -/
lemma lprod_altL (A : Matrix n n ℂ) (a : Bool) (m : ℕ) :
    lprod A (altL a (m + m)) = (ltr A a * ltr A (!a)) ^ m := by
  induction m with
  | zero => simp [altL, lprod]
  | succ k ih =>
    have h1 : k + 1 + (k + 1) = (k + k) + 2 := by omega
    rw [h1, altL_two_step, lprod_cons, lprod_cons, ih, pow_succ',
      ← Matrix.mul_assoc]

/-! ## Locating an equal adjacent pair and rotating it to the junction -/

/-- Lean implementation helper: a nonmaximal transition count yields an equal adjacent pair. -/
lemma exists_adj_eq {l : List Bool} (h : dtrans l + 1 < l.length) :
    ∃ j : ℕ, ∃ hj : j + 1 < l.length,
      l.get ⟨j, by omega⟩ = l.get ⟨j + 1, hj⟩ := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    cases t with
    | nil => simp [dtrans] at h
    | cons b t' =>
      by_cases hab : a = b
      · exact ⟨0, by simp, by simpa using hab⟩
      · have h3 : dd a b = 1 := by simp [dd, hab]
        have h4 : dtrans (b :: t') + 1 < (b :: t').length := by
          have h5 : dtrans (a :: b :: t') = dd a b + dtrans (b :: t') := rfl
          simp only [List.length_cons] at h ⊢
          omega
        obtain ⟨j, hj, hje⟩ := ih h4
        refine ⟨j + 1, by simpa using Nat.succ_lt_succ hj, ?_⟩
        simpa using hje

/-- Lean implementation helper.

If a word of length `m + m` is not fully (cyclically) alternating,
some rotation has an equal pair straddling the midpoint junction. -/
lemma exists_rotate_junction {l : List Bool} {m : ℕ} (hm : 0 < m)
    (hlen : l.length = m + m) (hlt : ctrans l < l.length) :
    ∃ r : ℕ,
      (l.rotate r).get ⟨m - 1, by rw [List.length_rotate, hlen]; omega⟩ =
      (l.rotate r).get ⟨m, by rw [List.length_rotate, hlen]; omega⟩ := by
  have hne : l ≠ [] := by
    intro h'
    subst h'
    simp at hlen
    omega
  by_cases hd : dtrans l + 1 < l.length
  · obtain ⟨j, hj, hje⟩ := exists_adj_eq hd
    refine ⟨j + m + 1, ?_⟩
    rw [List.get_rotate, List.get_rotate]
    have e1 : ((m - 1) + (j + m + 1)) % l.length = j := by
      rw [hlen]
      have h6 : (m - 1) + (j + m + 1) = j + (m + m) := by omega
      rw [h6, Nat.add_mod_right, Nat.mod_eq_of_lt (by rw [hlen] at hj; omega)]
    have e2 : (m + (j + m + 1)) % l.length = j + 1 := by
      rw [hlen]
      have h6 : m + (j + m + 1) = (j + 1) + (m + m) := by omega
      rw [h6, Nat.add_mod_right, Nat.mod_eq_of_lt (by rw [hlen] at hj; omega)]
    convert hje using 2
    · exact Fin.ext e1
    · exact Fin.ext e2
  · rw [not_lt] at hd
    have hdl := dtrans_lt_length hne
    have hdeq : dtrans l + 1 = l.length := by omega
    have h2 : 2 ≤ l.length := by omega
    have hwrap : l.getLast hne = l.head hne := by
      by_contra hne'
      have h7 : ctrans l = dtrans l + 1 := by
        rw [ctrans, dif_pos h2]
        have h8 : dd (l.getLast (by intro h'; subst h'; simp at h2))
            (l.head (by intro h'; subst h'; simp at h2)) = 1 := by
          simp [dd, hne']
        omega
      omega
    refine ⟨m, ?_⟩
    rw [List.get_rotate, List.get_rotate]
    have e1 : ((m - 1) + m) % l.length = l.length - 1 := by
      rw [hlen, Nat.mod_eq_of_lt (by omega)]
      omega
    have e2 : (m + m) % l.length = 0 := by
      rw [hlen, Nat.mod_self]
    have hLH : l.get ⟨l.length - 1, by omega⟩ = l.get ⟨0, by omega⟩ := by
      have hL : l.get ⟨l.length - 1, by omega⟩ = l.getLast hne := by
        rw [List.get_eq_getElem, List.getLast_eq_getElem]
      have hH : l.get ⟨0, by omega⟩ = l.head hne := by
        rw [List.get_eq_getElem, List.head_eq_getElem_zero hne]
      rw [hL, hH, hwrap]
    convert hLH using 2
    · exact Fin.ext e1
    · exact Fin.ext e2

/-! ## Words as functions, and the maximization argument -/

/-- Lean implementation helper.

The trace value of a word (as a function). -/
noncomputable def wtr (A : Matrix n n ℂ) {N : ℕ} (w : Fin N → Bool) : ℂ :=
  (lprod A (List.ofFn w)).trace

/-- Lean implementation helper.

`getLast` of a prefix as an entry of the original list. -/
lemma getLast_take_eq_get {α : Type*} (l : List α) {m : ℕ} (hm : 0 < m)
    (hml : m ≤ l.length) (hne : l.take m ≠ []) :
    (l.take m).getLast hne = l.get ⟨m - 1, by omega⟩ := by
  rw [List.getLast_eq_getElem, List.get_eq_getElem]
  rw [List.getElem_take]
  congr 1
  rw [List.length_take]
  show min m l.length - 1 = m - 1
  omega

/-- Lean implementation helper.

`head` of a suffix as an entry of the original list. -/
lemma head_drop_eq_get {α : Type*} (l : List α) {m : ℕ} (hml : m < l.length)
    (hne : l.drop m ≠ []) :
    (l.drop m).head hne = l.get ⟨m, hml⟩ := by
  rw [List.head_eq_getElem_zero hne, List.get_eq_getElem, List.getElem_drop]
  simp

/-- Lean implementation helper.

Repackaging a length-`m + m` list as a word function. -/
def wordOfList (m : ℕ) (l : List Bool) (hl : l.length = m + m) :
    Fin (m + m) → Bool :=
  fun i => l.get ⟨i, by rw [hl]; exact i.isLt⟩

/-- Lean implementation helper. -/
lemma ofFn_wordOfList (m : ℕ) (l : List Bool) (hl : l.length = m + m) :
    List.ofFn (wordOfList m l hl) = l := by
  refine List.ext_get (by simp [hl]) ?_
  intro i h1 h2
  simp [wordOfList]

/-- Lean implementation helper.

**Dyson's disentangling lemma** (Dyson 1964; Lee, CSE 599I Lecture 3,
Lemma 1.3): every word of length `2m` in the letters `{A, Aᴴ}` has trace
dominated by the fully disentangled word:
`‖tr(A₁A₂⋯A_{2m})‖ ≤ tr((AᴴA)^m)`. -/
theorem dyson_bound (A : Matrix n n ℂ) (m : ℕ) (hm : 0 < m)
    (w : Fin (m + m) → Bool) :
    ‖wtr A w‖ ≤ (((Aᴴ * A) ^ m).trace).re := by
  classical
  set T := (((Aᴴ * A) ^ m).trace).re with hT
  have hTnn : 0 ≤ T :=
    trace_re_nonneg_of_posSemidef
      ((Matrix.posSemidef_conjTranspose_mul_self A).pow m)
  -- a global maximizer of the trace norm over all words
  obtain ⟨w₀, -, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (m + m) → Bool)) (fun v => ‖wtr A v‖)
    ⟨fun _ => false, Finset.mem_univ _⟩
  set Mx := ‖wtr A w₀‖ with hMx
  suffices hMT : Mx ≤ T by
    exact le_trans (hmax w (Finset.mem_univ w)) hMT
  by_contra hcon
  rw [not_le] at hcon
  have hMxpos : 0 < Mx := lt_of_le_of_lt hTnn hcon
  -- among the maximizers, one with the largest cyclic transition count
  set MS : Finset (Fin (m + m) → Bool) :=
    Finset.univ.filter (fun v => ‖wtr A v‖ = Mx) with hMS
  have hMSne : MS.Nonempty := ⟨w₀, by
    rw [hMS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hMx.symm⟩⟩
  obtain ⟨w₁, hw₁mem, hw₁max⟩ := Finset.exists_max_image MS
    (fun v => ctrans (List.ofFn v)) hMSne
  have hw₁val : ‖wtr A w₁‖ = Mx := by
    have := hw₁mem
    rw [hMS, Finset.mem_filter] at this
    exact this.2
  set l₁ := List.ofFn w₁ with hl₁
  have hlen₁ : l₁.length = m + m := by simp [hl₁]
  have hl₁ne : l₁ ≠ [] := by
    intro h'
    rw [h'] at hlen₁
    simp at hlen₁
    omega
  by_cases hct : ctrans l₁ = m + m
  · -- fully alternating: the maximal value is `T` itself — contradiction
    have hd1 := dtrans_lt_length hl₁ne
    have hd2 := ctrans_le_dtrans_add_one l₁
    have hdeq : dtrans l₁ + 1 = l₁.length := by
      rw [hlen₁]
      rw [hlen₁] at hd1
      omega
    have halt := eq_altL_of_dtrans_max l₁ hl₁ne hdeq
    have hprod : lprod A l₁ =
        (ltr A (l₁.head hl₁ne) * ltr A (!(l₁.head hl₁ne))) ^ m := by
      conv_lhs => rw [halt, hlen₁]
      exact lprod_altL A _ m
    have htr : ‖wtr A w₁‖ = T := by
      rw [wtr, ← hl₁, hprod]
      cases hh : (l₁.head hl₁ne)
      · -- (A · Aᴴ)^m
        simp only [ltr_false, ltr_true, Bool.not_false]
        rw [norm_trace_of_posSemidef
          ((Matrix.posSemidef_self_mul_conjTranspose A).pow m), hT]
        rw [show ((A * Aᴴ) ^ m).trace = ((Aᴴ * A) ^ m).trace from
          trace_pow_mul_comm A Aᴴ m]
      · -- (Aᴴ · A)^m
        simp only [ltr_true, ltr_false, Bool.not_true]
        rw [norm_trace_of_posSemidef
          ((Matrix.posSemidef_conjTranspose_mul_self A).pow m), hT]
    rw [hw₁val] at htr
    exact absurd htr (ne_of_gt hcon)
  · -- not alternating: rotate an equal pair to the junction and split
    have hctlt : ctrans l₁ < m + m :=
      lt_of_le_of_ne (hlen₁ ▸ ctrans_le_length l₁) hct
    obtain ⟨r, hjunc⟩ := exists_rotate_junction hm hlen₁ (hlen₁ ▸ hctlt)
    set l₂ := l₁.rotate r with hl₂
    have hlen₂ : l₂.length = m + m := by rw [hl₂, List.length_rotate, hlen₁]
    set Q := l₂.take m with hQdef
    set R := l₂.drop m with hRdef
    have hQlen : Q.length = m := by
      rw [hQdef, List.length_take, hlen₂]
      omega
    have hRlen : R.length = m := by
      rw [hRdef, List.length_drop, hlen₂]
      omega
    have hQne : Q ≠ [] := by
      intro h'
      rw [h'] at hQlen
      simp at hQlen
      omega
    have hRne : R ≠ [] := by
      intro h'
      rw [h'] at hRlen
      simp at hRlen
      omega
    have hQR : Q ++ R = l₂ := List.take_append_drop m l₂
    -- the rotated word still attains the maximum
    have hval₂ : ‖(lprod A l₂).trace‖ = Mx := by
      rw [hl₂, trace_lprod_rotate]
      rw [show (lprod A l₁).trace = wtr A w₁ from by rw [wtr, hl₁]]
      exact hw₁val
    -- the junction is an equal pair
    have hjunc' : Q.getLast hQne = R.head hRne := by
      have hgl := getLast_take_eq_get l₂ hm (by rw [hlen₂]; omega) hQne
      have hhd := head_drop_eq_get l₂ (m := m) (by rw [hlen₂]; omega) hRne
      rw [hgl, hhd]
      exact hjunc
    -- Cauchy–Schwarz across the junction
    have hCS : Mx ≤ Real.sqrt (((lprod A Q)ᴴ * lprod A Q).trace).re *
        Real.sqrt (((lprod A R)ᴴ * lprod A R).trace).re := by
      rw [← hval₂, ← hQR, lprod_append]
      exact trace_mul_le_frob _ _
    -- the two star-words and their values
    set P1 : List Bool := (Q.reverse.map (! ·)) ++ Q with hP1
    set P2 : List Bool := (R.reverse.map (! ·)) ++ R with hP2
    have hP1len : P1.length = m + m := by
      rw [hP1]
      simp [hQlen]
    have hP2len : P2.length = m + m := by
      rw [hP2]
      simp [hRlen]
    have hP1prod : lprod A P1 = (lprod A Q)ᴴ * lprod A Q := by
      rw [hP1, lprod_append, ← lprod_star]
    have hP2prod : lprod A P2 = (lprod A R)ᴴ * lprod A R := by
      rw [hP2, lprod_append, ← lprod_star]
    have hP1re : (((lprod A Q)ᴴ * lprod A Q).trace).re =
        ‖wtr A (wordOfList m P1 hP1len)‖ := by
      rw [wtr, ofFn_wordOfList, hP1prod,
        norm_trace_of_posSemidef
          (Matrix.posSemidef_conjTranspose_mul_self (lprod A Q))]
    have hP2re : (((lprod A R)ᴴ * lprod A R).trace).re =
        ‖wtr A (wordOfList m P2 hP2len)‖ := by
      rw [wtr, ofFn_wordOfList, hP2prod,
        norm_trace_of_posSemidef
          (Matrix.posSemidef_conjTranspose_mul_self (lprod A R))]
    have hP1le : (((lprod A Q)ᴴ * lprod A Q).trace).re ≤ Mx := by
      rw [hP1re]
      exact hmax _ (Finset.mem_univ _)
    have hP2le : (((lprod A R)ᴴ * lprod A R).trace).re ≤ Mx := by
      rw [hP2re]
      exact hmax _ (Finset.mem_univ _)
    have hP1nn : 0 ≤ (((lprod A Q)ᴴ * lprod A Q).trace).re :=
      trace_re_nonneg_of_posSemidef
        (Matrix.posSemidef_conjTranspose_mul_self _)
    have hP2nn : 0 ≤ (((lprod A R)ᴴ * lprod A R).trace).re :=
      trace_re_nonneg_of_posSemidef
        (Matrix.posSemidef_conjTranspose_mul_self _)
    -- the squeeze: both split values must equal the maximum
    have hP1eq : (((lprod A Q)ᴴ * lprod A Q).trace).re = Mx := by
      by_contra hne'
      have hlt : (((lprod A Q)ᴴ * lprod A Q).trace).re < Mx :=
        lt_of_le_of_ne hP1le hne'
      have hs1 : Real.sqrt (((lprod A Q)ᴴ * lprod A Q).trace).re <
          Real.sqrt Mx := Real.sqrt_lt_sqrt hP1nn hlt
      have hs2 : Real.sqrt (((lprod A R)ᴴ * lprod A R).trace).re ≤
          Real.sqrt Mx := Real.sqrt_le_sqrt hP2le
      have hbig : Real.sqrt (((lprod A Q)ᴴ * lprod A Q).trace).re *
          Real.sqrt (((lprod A R)ᴴ * lprod A R).trace).re <
          Real.sqrt Mx * Real.sqrt Mx :=
        calc Real.sqrt (((lprod A Q)ᴴ * lprod A Q).trace).re *
            Real.sqrt (((lprod A R)ᴴ * lprod A R).trace).re
            ≤ Real.sqrt (((lprod A Q)ᴴ * lprod A Q).trace).re *
              Real.sqrt Mx :=
              mul_le_mul_of_nonneg_left hs2 (Real.sqrt_nonneg _)
          _ < Real.sqrt Mx * Real.sqrt Mx :=
              mul_lt_mul_of_pos_right hs1 (Real.sqrt_pos.mpr hMxpos)
      rw [Real.mul_self_sqrt (le_of_lt hMxpos)] at hbig
      exact absurd (lt_of_le_of_lt hCS hbig) (lt_irrefl _)
    have hP2eq : (((lprod A R)ᴴ * lprod A R).trace).re = Mx := by
      by_contra hne'
      have hlt : (((lprod A R)ᴴ * lprod A R).trace).re < Mx :=
        lt_of_le_of_ne hP2le hne'
      have hs1 : Real.sqrt (((lprod A R)ᴴ * lprod A R).trace).re <
          Real.sqrt Mx := Real.sqrt_lt_sqrt hP2nn hlt
      have hs2 : Real.sqrt (((lprod A Q)ᴴ * lprod A Q).trace).re ≤
          Real.sqrt Mx := Real.sqrt_le_sqrt hP1le
      have hbig : Real.sqrt (((lprod A Q)ᴴ * lprod A Q).trace).re *
          Real.sqrt (((lprod A R)ᴴ * lprod A R).trace).re <
          Real.sqrt Mx * Real.sqrt Mx :=
        calc Real.sqrt (((lprod A Q)ᴴ * lprod A Q).trace).re *
            Real.sqrt (((lprod A R)ᴴ * lprod A R).trace).re
            ≤ Real.sqrt Mx *
              Real.sqrt (((lprod A R)ᴴ * lprod A R).trace).re :=
              mul_le_mul_of_nonneg_right hs2 (Real.sqrt_nonneg _)
          _ < Real.sqrt Mx * Real.sqrt Mx :=
              mul_lt_mul_of_pos_left hs1 (Real.sqrt_pos.mpr hMxpos)
      rw [Real.mul_self_sqrt (le_of_lt hMxpos)] at hbig
      exact absurd (lt_of_le_of_lt hCS hbig) (lt_irrefl _)
    -- both split words are maximizers, but their transition counts are
    -- too large: contradiction with the maximality of `w₁`
    have hP1mem : wordOfList m P1 hP1len ∈ MS := by
      rw [hMS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [← hP1re, hP1eq]⟩
    have hP2mem : wordOfList m P2 hP2len ∈ MS := by
      rw [hMS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [← hP2re, hP2eq]⟩
    have h1 := hw₁max _ hP1mem
    have h2 := hw₁max _ hP2mem
    rw [ofFn_wordOfList] at h1 h2
    have hc1 : ctrans P1 = 2 * dtrans Q + 2 := by
      rw [hP1]
      exact ctrans_starword Q hQne
    have hc2 : ctrans P2 = 2 * dtrans R + 2 := by
      rw [hP2]
      exact ctrans_starword R hRne
    have hsplit : ctrans l₂ ≤ dtrans Q + dtrans R + 1 := by
      rw [← hQR]
      exact ctrans_split_le Q R hQne hRne hjunc'
    have hrot : ctrans l₂ = ctrans l₁ := by
      rw [hl₂, ctrans_rotate]
    omega

end Dyson

/-! ## The disentangling chain (Lee, Lemma 1.2) -/

/-- Lean implementation helper.

Dyson's bound specialized to the constant word: `‖tr(A^{2m})‖ ≤
tr((AᴴA)^m).re`. -/
theorem dyson_all_letters (A : Matrix n n ℂ) (m : ℕ) (hm : 0 < m) :
    ‖((A ^ (m + m) : Matrix n n ℂ)).trace‖ ≤ (((Aᴴ * A) ^ m).trace).re := by
  have h := Dyson.dyson_bound A m hm (fun _ => false)
  have h2 : Dyson.wtr A (fun _ : Fin (m + m) => false) =
      (A ^ (m + m)).trace := by
    rw [Dyson.wtr]
    congr 1
    rw [Dyson.lprod, List.ofFn_const]
    simp [List.map_replicate, List.prod_replicate]
  rwa [h2] at h

/-- Lean implementation helper.

**Disentangling** (Lee, CSE 599I Lecture 3, Lemma 1.2): for Hermitian
`U`, `V` and every `k ≥ 1`,
`‖tr((UV)^{2^k})‖ ≤ tr(U^{2^k} V^{2^k}).re`. -/
theorem disentangle :
    ∀ k : ℕ, 1 ≤ k → ∀ U V : Matrix n n ℂ, U.IsHermitian → V.IsHermitian →
      ‖((U * V) ^ (2 ^ k)).trace‖ ≤
        ((U ^ (2 ^ k) * V ^ (2 ^ k)).trace).re := by
  intro k
  induction k with
  | zero => omega
  | succ j ih =>
    intro _ U V hU hV
    have hm : 0 < 2 ^ j := by positivity
    have hsplit : (2 : ℕ) ^ (j + 1) = 2 ^ j + 2 ^ j := by
      rw [pow_succ]
      omega
    have hstep := dyson_all_letters (U * V) (2 ^ j) hm
    rw [← hsplit] at hstep
    have hUV : (U * V)ᴴ * (U * V) = V * (U * U * V) := by
      rw [Matrix.conjTranspose_mul, hU.eq, hV.eq]
      noncomm_ring
    rw [hUV] at hstep
    have hcyc : ((V * (U * U * V)) ^ (2 ^ j)).trace =
        (((U * U) * (V * V)) ^ (2 ^ j)).trace := by
      rw [trace_pow_mul_comm,
        show (U * U * V) * V = (U * U) * (V * V) from by noncomm_ring]
    rw [hcyc] at hstep
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      norm_num at hstep ⊢
      rw [pow_two U, pow_two V]
      exact hstep
    · have hU2 : (U * U).IsHermitian := by
        show _ᴴ = _
        rw [Matrix.conjTranspose_mul, hU.eq]
      have hV2 : (V * V).IsHermitian := by
        show _ᴴ = _
        rw [Matrix.conjTranspose_mul, hV.eq]
      have hih := ih hj (U * U) (V * V) hU2 hV2
      have hre : ((((U * U) * (V * V)) ^ (2 ^ j)).trace).re ≤
          ‖(((U * U) * (V * V)) ^ (2 ^ j)).trace‖ :=
        Complex.re_le_norm _
      have hfinal : (U * U) ^ (2 ^ j) * (V * V) ^ (2 ^ j) =
          U ^ (2 ^ (j + 1)) * V ^ (2 ^ (j + 1)) := by
        rw [← sq U, ← sq V, ← pow_mul, ← pow_mul]
        congr 2 <;> · rw [pow_succ]; ring
      calc ‖((U * V) ^ 2 ^ (j + 1)).trace‖
          ≤ ((((U * U) * (V * V)) ^ (2 ^ j)).trace).re := hstep
        _ ≤ ‖(((U * U) * (V * V)) ^ (2 ^ j)).trace‖ := hre
        _ ≤ (((U * U) ^ (2 ^ j) * (V * V) ^ (2 ^ j)).trace).re := hih
        _ = ((U ^ (2 ^ (j + 1)) * V ^ (2 ^ (j + 1))).trace).re := by
            rw [hfinal]

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Appendix A.3: The Golden–Thompson inequality

`tr e^{A+B} ≤ tr(e^A e^B)` for Hermitian `A`, `B` — Book equation
(3.3.3), consumed by the Chapter 3 module.

Proof (classical; see Golden 1965, Thompson 1965; the elementary
presentation followed here is J. R. Lee, *CSE 599I* (Spring 2021),
Lecture 3, which follows Dyson's disentangling argument; also
S. Golden, "Lower bounds for the Helmholtz function"; T. Tao's notes on
the Golden–Thompson inequality):

1. the **Lie product formula** `e^{A+B} = lim_N (e^{A/N} e^{B/N})^N`,
   here quantitatively: for `N ≥ 1`,
   `‖e^{(A+B)/N} − e^{A/N}e^{B/N}‖ = O(1/N²)`, whence
   `‖e^{A+B} − (e^{A/N}e^{B/N})^N‖ = O(1/N)` (second-order Taylor
   estimates for the exponential series, and a telescoping bound for
   powers);
2. the **disentangling chain** (`disentangle`, Appendix A.2, from
   Dyson's lemma): for the pd Hermitian matrices `U = e^{A/2^k}`,
   `V = e^{B/2^k}`, `tr((UV)^{2^k}) ≤ tr(U^{2^k}V^{2^k}) = tr(e^A e^B)`;
3. passing to the limit along `N = 2^k`.
-/

namespace MatrixConcentration

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Second-order estimates for the matrix exponential -/

section ExpEstimates

/-- Lean implementation helper.

`‖1‖ ≤ 1` for the L2 operator norm (also when `n` is empty). -/
lemma l2_norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  refine l2_opNorm_le_bound _ zero_le_one fun x => ?_
  rw [Matrix.one_mulVec, one_mul]

/-- Lean implementation helper.

`‖X^k‖ ≤ ‖X‖^k` for every `k` (without `NormOneClass`). -/
lemma norm_pow_le_norm_pow (X : Matrix n n ℂ) (k : ℕ) :
    ‖X ^ k‖ ≤ ‖X‖ ^ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simpa using l2_norm_one_le
  · exact norm_pow_le' X hk

/-- Lean implementation helper.

The exponential series bound `‖e^X‖ ≤ e^{‖X‖}`. -/
lemma norm_exp_le_exp_norm (X : Matrix n n ℂ) :
    ‖NormedSpace.exp X‖ ≤ Real.exp ‖X‖ := by
  have hsum := NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) X
  have hfac := Real.summable_pow_div_factorial ‖X‖
  rw [congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ)) X]
  refine le_trans (norm_tsum_le_tsum_norm hsum) ?_
  rw [Real.exp_eq_exp_ℝ, congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ)) ‖X‖]
  have hsumR : Summable (fun k : ℕ => (k.factorial : ℝ)⁻¹ • ‖X‖ ^ k) := by
    refine hfac.congr fun k => ?_
    rw [smul_eq_mul]
    ring
  refine Summable.tsum_mono hsum hsumR fun k => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le_norm_pow X k)
    (by positivity)

/-- Lean implementation helper.

Second-order Taylor estimate: `‖e^X − 1 − X‖ ≤ ‖X‖² e^{‖X‖}`. -/
lemma norm_exp_sub_one_sub_le (X : Matrix n n ℂ) :
    ‖NormedSpace.exp X - 1 - X‖ ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ := by
  have hsum := NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) X
  have hsum' : Summable (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • X ^ k) :=
    hsum.of_norm
  -- split off the first two terms
  have hsplit := hsum'.sum_add_tsum_nat_add 2
  have hfirst : ∑ i ∈ Finset.range 2,
      ((i.factorial : ℝ)⁻¹) • X ^ i = 1 + X := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp
  have hexp : NormedSpace.exp X - 1 - X =
      ∑' k : ℕ, ((k + 2).factorial : ℝ)⁻¹ • X ^ (k + 2) := by
    rw [congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ)) X, ← hsplit, hfirst]
    abel
  rw [hexp]
  have htail : Summable (fun k : ℕ =>
      ‖((k + 2).factorial : ℝ)⁻¹ • X ^ (k + 2)‖) :=
    (summable_nat_add_iff 2).mpr hsum
  refine le_trans (norm_tsum_le_tsum_norm htail) ?_
  have hbound : ∀ k : ℕ, ‖((k + 2).factorial : ℝ)⁻¹ • X ^ (k + 2)‖ ≤
      ‖X‖ ^ 2 * (‖X‖ ^ k / k.factorial) := by
    intro k
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖X ^ (k + 2)‖ ≤ ‖X‖ ^ (k + 2) := norm_pow_le_norm_pow X (k + 2)
    have h2 : ((k + 2).factorial : ℝ)⁻¹ ≤ (k.factorial : ℝ)⁻¹ := by
      have h3 : (k.factorial : ℝ) ≤ ((k + 2).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega)
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) h3
    calc ((k + 2).factorial : ℝ)⁻¹ * ‖X ^ (k + 2)‖
        ≤ (k.factorial : ℝ)⁻¹ * ‖X‖ ^ (k + 2) := by
          exact mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = ‖X‖ ^ 2 * (‖X‖ ^ k / k.factorial) := by
          rw [pow_add]
          ring
  have hbig : Summable (fun k : ℕ => ‖X‖ ^ 2 * (‖X‖ ^ k / k.factorial)) :=
    (Real.summable_pow_div_factorial ‖X‖).mul_left _
  refine le_trans (Summable.tsum_mono htail hbig hbound) ?_
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Real.exp_eq_exp_ℝ, congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ)) ‖X‖]
  refine le_of_eq (tsum_congr fun k => ?_)
  rw [smul_eq_mul]
  ring

end ExpEstimates

/-! ## The Lie product formula, quantitatively -/

section Trotter

/-- Lean implementation helper.

The scaled matrix `X/N` (real scalar multiplication, preserving
Hermitian structure). -/
noncomputable def scDiv (N : ℕ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  ((N : ℝ)⁻¹) • X

/-- Lean implementation helper. -/
lemma scDiv_isHermitian {X : Matrix n n ℂ} (hX : X.IsHermitian) (N : ℕ) :
    (scDiv N X).IsHermitian := by
  show _ᴴ = _
  rw [scDiv, Matrix.conjTranspose_smul, star_trivial, hX.eq]

/-- Lean implementation helper. -/
lemma scDiv_add (N : ℕ) (X Y : Matrix n n ℂ) :
    scDiv N (X + Y) = scDiv N X + scDiv N Y := by
  rw [scDiv, scDiv, scDiv, smul_add]

/-- Lean implementation helper. -/
lemma norm_scDiv (N : ℕ) (X : Matrix n n ℂ) :
    ‖scDiv N X‖ = ‖X‖ / N := by
  rw [scDiv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_eq_inv_mul]

/-- Lean implementation helper.

`(e^X)^N = e^{N•X}` (via the `ℂ`-ball variant of `exp_add`, since the
`ℚ`-normed-algebra instance is unavailable for matrices). -/
lemma exp_pow_nsmul (X : Matrix n n ℂ) :
    ∀ N : ℕ, (NormedSpace.exp X) ^ N = NormedSpace.exp ((N : ℕ) • X)
  | 0 => by simp
  | N + 1 => by
    rw [pow_succ, exp_pow_nsmul X N, succ_nsmul,
      NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
        ((Commute.refl X).smul_left N)
        ((NormedSpace.expSeries_radius_eq_top ℂ
          (Matrix n n ℂ)).symm ▸ edist_lt_top _ _)
        ((NormedSpace.expSeries_radius_eq_top ℂ
          (Matrix n n ℂ)).symm ▸ edist_lt_top _ _)]

/-- Lean implementation helper. -/
lemma exp_scDiv_pow (N : ℕ) (hN : N ≠ 0) (X : Matrix n n ℂ) :
    (NormedSpace.exp (scDiv N X)) ^ N = NormedSpace.exp X := by
  rw [exp_pow_nsmul]
  congr 1
  rw [scDiv, ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_smul,
    mul_inv_cancel₀ (by exact_mod_cast hN), one_smul]

/-- Lean implementation helper.

The constant of the one-step Trotter estimate. -/
noncomputable def trotterC (A B : Matrix n n ℂ) : ℝ :=
  3 * ((‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖)) + (‖A‖ + ‖B‖) ^ 2 +
    2 * ((‖A‖ + ‖B‖) * ((‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖))) +
    ((‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖)) ^ 2

/-- Lean implementation helper. -/
lemma trotterC_nonneg (A B : Matrix n n ℂ) : 0 ≤ trotterC A B := by
  rw [trotterC]
  positivity

/-- Lean implementation helper.

**One-step Trotter estimate**  for `N ≥ 1`,
`‖e^{(A+B)/N} − e^{A/N} e^{B/N}‖ ≤ trotterC A B / N²`. -/
lemma trotter_step (A B : Matrix n n ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ‖NormedSpace.exp (scDiv N (A + B)) -
      NormedSpace.exp (scDiv N A) * NormedSpace.exp (scDiv N B)‖ ≤
      trotterC A B / (N : ℝ) ^ 2 := by
  set c := ‖A‖ + ‖B‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  set E := c ^ 2 * Real.exp c with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  set t := ((N : ℝ))⁻¹ with ht
  have ht0 : 0 < t := by
    rw [ht]
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have ht1 : t ≤ 1 := by
    rw [ht]
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [inv_le_one_iff₀]
    right
    exact h1
  set u := scDiv N A with hu
  set v := scDiv N B with hv
  -- basic norms
  have hnu : ‖u‖ ≤ c * t := by
    rw [hu, norm_scDiv, div_eq_mul_inv, ← ht]
    have : ‖A‖ ≤ c := by rw [hc]; nlinarith [norm_nonneg B]
    exact mul_le_mul_of_nonneg_right this (le_of_lt ht0)
  have hnv : ‖v‖ ≤ c * t := by
    rw [hv, norm_scDiv, div_eq_mul_inv, ← ht]
    have : ‖B‖ ≤ c := by rw [hc]; nlinarith [norm_nonneg A]
    exact mul_le_mul_of_nonneg_right this (le_of_lt ht0)
  have hnw : ‖u + v‖ ≤ c * t := by
    rw [hu, hv, ← scDiv_add, norm_scDiv, div_eq_mul_inv, ← ht]
    have : ‖A + B‖ ≤ c := by rw [hc]; exact norm_add_le A B
    exact mul_le_mul_of_nonneg_right this (le_of_lt ht0)
  have hct_le_c : c * t ≤ c := by nlinarith
  -- the three remainders
  set RA := NormedSpace.exp u - 1 - u with hRA
  set RB := NormedSpace.exp v - 1 - v with hRB
  set RW := NormedSpace.exp (u + v) - 1 - (u + v) with hRW
  have hexp_mono : ∀ Y : Matrix n n ℂ, ‖Y‖ ≤ c * t →
      ‖NormedSpace.exp Y - 1 - Y‖ ≤ E * t ^ 2 := by
    intro Y hY
    refine le_trans (norm_exp_sub_one_sub_le Y) ?_
    have h1 : ‖Y‖ ^ 2 ≤ (c * t) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hY 2
    have h2 : Real.exp ‖Y‖ ≤ Real.exp c :=
      Real.exp_le_exp.mpr (le_trans hY hct_le_c)
    calc ‖Y‖ ^ 2 * Real.exp ‖Y‖ ≤ (c * t) ^ 2 * Real.exp c := by
          exact mul_le_mul h1 h2 (le_of_lt (Real.exp_pos _)) (by positivity)
      _ = E * t ^ 2 := by rw [hE]; ring
  have hnRA : ‖RA‖ ≤ E * t ^ 2 := hexp_mono u hnu
  have hnRB : ‖RB‖ ≤ E * t ^ 2 := hexp_mono v hnv
  have hnRW : ‖RW‖ ≤ E * t ^ 2 := hexp_mono (u + v) hnw
  -- the algebraic identity
  have hD : NormedSpace.exp (u + v) -
      NormedSpace.exp u * NormedSpace.exp v =
      RW - (u * v + u * RB + RA + RA * v + RA * RB + RB) := by
    rw [hRA, hRB, hRW]
    noncomm_ring
  have harg : scDiv N (A + B) = u + v := by rw [scDiv_add, hu, hv]
  rw [harg, hD]
  -- assemble the bound
  have hS : ‖u * v + u * RB + RA + RA * v + RA * RB + RB‖ ≤
      ‖u‖ * ‖v‖ + ‖u‖ * ‖RB‖ + ‖RA‖ + ‖RA‖ * ‖v‖ + ‖RA‖ * ‖RB‖ + ‖RB‖ := by
    have h1 := norm_add_le (u * v + u * RB + RA + RA * v + RA * RB) RB
    have h2 := norm_add_le (u * v + u * RB + RA + RA * v) (RA * RB)
    have h3 := norm_add_le (u * v + u * RB + RA) (RA * v)
    have h4 := norm_add_le (u * v + u * RB) RA
    have h5 := norm_add_le (u * v) (u * RB)
    have m1 := norm_mul_le u v
    have m2 := norm_mul_le u RB
    have m3 := norm_mul_le RA v
    have m4 := norm_mul_le RA RB
    linarith
  have htotal : ‖RW - (u * v + u * RB + RA + RA * v + RA * RB + RB)‖ ≤
      ‖RW‖ + (‖u‖ * ‖v‖ + ‖u‖ * ‖RB‖ + ‖RA‖ + ‖RA‖ * ‖v‖ + ‖RA‖ * ‖RB‖ +
        ‖RB‖) := le_trans (norm_sub_le _ _) (by linarith)
  refine le_trans htotal ?_
  -- numerical bound: everything is `O(t²)`
  have hnu' : 0 ≤ ‖u‖ := norm_nonneg _
  have hnv' : 0 ≤ ‖v‖ := norm_nonneg _
  have hnRA' : 0 ≤ ‖RA‖ := norm_nonneg _
  have hnRB' : 0 ≤ ‖RB‖ := norm_nonneg _
  have hkey : ‖RW‖ + (‖u‖ * ‖v‖ + ‖u‖ * ‖RB‖ + ‖RA‖ + ‖RA‖ * ‖v‖ +
      ‖RA‖ * ‖RB‖ + ‖RB‖) ≤
      (3 * E + c ^ 2 + 2 * (c * E) + E ^ 2) * t ^ 2 := by
    have b1 : ‖u‖ * ‖v‖ ≤ (c * t) * (c * t) :=
      mul_le_mul hnu hnv hnv' (by positivity)
    have b2 : ‖u‖ * ‖RB‖ ≤ (c * t) * (E * t ^ 2) :=
      mul_le_mul hnu hnRB hnRB' (by positivity)
    have b3 : ‖RA‖ * ‖v‖ ≤ (E * t ^ 2) * (c * t) :=
      mul_le_mul hnRA hnv hnv' (by positivity)
    have b4 : ‖RA‖ * ‖RB‖ ≤ (E * t ^ 2) * (E * t ^ 2) :=
      mul_le_mul hnRA hnRB hnRB' (by positivity)
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have ht3 : t ^ 3 ≤ t ^ 2 := by nlinarith
    have ht4 : t ^ 4 ≤ t ^ 2 := by nlinarith
    nlinarith [mul_nonneg hE0 (le_of_lt ht0), mul_nonneg hc0 hE0,
      mul_nonneg (mul_nonneg hc0 hE0) (le_of_lt ht0), sq_nonneg t,
      mul_nonneg hc0 (le_of_lt ht0), mul_le_mul_of_nonneg_left ht3
        (mul_nonneg hc0 hE0), mul_le_mul_of_nonneg_left ht4
        (mul_nonneg hE0 hE0)]
  refine le_trans hkey ?_
  rw [trotterC, ← hc, ← hE, div_eq_mul_inv]
  have h9 : ((N : ℝ) ^ 2)⁻¹ = t ^ 2 := by
    rw [ht, ← inv_pow]
  rw [h9]

/-- Lean implementation helper.

Telescoping bound for powers: if `‖U‖, ‖V‖ ≤ ρ` with `ρ ≥ 1`, then
`‖U^N − V^N‖ ≤ N ρ^N ‖U − V‖`. -/
lemma pow_diff_norm_le (U V : Matrix n n ℂ) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hU : ‖U‖ ≤ ρ) (hV : ‖V‖ ≤ ρ) :
    ∀ N : ℕ, ‖U ^ N - V ^ N‖ ≤ N * ρ ^ N * ‖U - V‖ := by
  intro N
  induction N with
  | zero => simp
  | succ k ih =>
    have hρ0 : 0 ≤ ρ := le_trans zero_le_one hρ
    have h1 : U ^ (k + 1) - V ^ (k + 1) =
        U ^ k * (U - V) + (U ^ k - V ^ k) * V := by noncomm_ring
    have h2 : ‖U ^ k * (U - V)‖ ≤ ρ ^ k * ‖U - V‖ := by
      refine le_trans (norm_mul_le _ _) ?_
      exact mul_le_mul_of_nonneg_right (le_trans (norm_pow_le_norm_pow U k)
        (pow_le_pow_left₀ (norm_nonneg _) hU k)) (norm_nonneg _)
    have h3 : ‖(U ^ k - V ^ k) * V‖ ≤ (k * ρ ^ k * ‖U - V‖) * ρ := by
      refine le_trans (norm_mul_le _ _) ?_
      exact mul_le_mul ih hV (norm_nonneg _)
        (by positivity)
    calc ‖U ^ (k + 1) - V ^ (k + 1)‖
        ≤ ‖U ^ k * (U - V)‖ + ‖(U ^ k - V ^ k) * V‖ := by
          rw [h1]
          exact norm_add_le _ _
      _ ≤ ρ ^ k * ‖U - V‖ + (k * ρ ^ k * ‖U - V‖) * ρ := by linarith
      _ ≤ (k + 1 : ℕ) * ρ ^ (k + 1) * ‖U - V‖ := by
          have hρk1 : ρ ^ k ≤ ρ ^ (k + 1) := by
            calc ρ ^ k = ρ ^ k * 1 := by ring
              _ ≤ ρ ^ k * ρ := by
                  exact mul_le_mul_of_nonneg_left hρ (by positivity)
              _ = ρ ^ (k + 1) := by rw [pow_succ]
          have hnn : 0 ≤ ‖U - V‖ := norm_nonneg _
          have key : ρ ^ k * ‖U - V‖ ≤ ρ ^ (k + 1) * ‖U - V‖ :=
            mul_le_mul_of_nonneg_right hρk1 hnn
          have e1 : ((k : ℕ) : ℝ) * ρ ^ k * ‖U - V‖ * ρ =
              ((k : ℕ) : ℝ) * (ρ ^ (k + 1) * ‖U - V‖) := by
            rw [pow_succ]
            ring
          have e2 : (((k : ℕ) : ℝ) + 1) * (ρ ^ (k + 1) * ‖U - V‖) =
              ((k : ℕ) : ℝ) * (ρ ^ (k + 1) * ‖U - V‖) +
                ρ ^ (k + 1) * ‖U - V‖ := by ring
          have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg k
          push_cast
          calc ρ ^ k * ‖U - V‖ + ((k : ℕ) : ℝ) * ρ ^ k * ‖U - V‖ * ρ
              = ρ ^ k * ‖U - V‖ +
                ((k : ℕ) : ℝ) * (ρ ^ (k + 1) * ‖U - V‖) := by rw [e1]
            _ ≤ ρ ^ (k + 1) * ‖U - V‖ +
                ((k : ℕ) : ℝ) * (ρ ^ (k + 1) * ‖U - V‖) := by linarith
            _ = (((k : ℕ) : ℝ) + 1) * ρ ^ (k + 1) * ‖U - V‖ := by ring

/-- Lean implementation helper.

**Lie product formula, quantitative form**  for `N ≥ 1`,
`‖e^{A+B} − (e^{A/N} e^{B/N})^N‖ ≤ e^{‖A‖+‖B‖} · trotterC A B / N`. -/
theorem trotter_bound (A B : Matrix n n ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ‖NormedSpace.exp (A + B) -
      (NormedSpace.exp (scDiv N A) * NormedSpace.exp (scDiv N B)) ^ N‖ ≤
      Real.exp (‖A‖ + ‖B‖) * trotterC A B / N := by
  have hN0 : N ≠ 0 := by omega
  set U := NormedSpace.exp (scDiv N (A + B)) with hU
  set V := NormedSpace.exp (scDiv N A) * NormedSpace.exp (scDiv N B) with hV
  set c := ‖A‖ + ‖B‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  set ρ := Real.exp (c / N) with hρdef
  have hρ1 : 1 ≤ ρ := by
    rw [hρdef]
    exact Real.one_le_exp (by positivity)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  -- norm bounds for U and V
  have hUn : ‖U‖ ≤ ρ := by
    rw [hU, hρdef]
    refine le_trans (norm_exp_le_exp_norm _) (Real.exp_le_exp.mpr ?_)
    rw [norm_scDiv]
    have h1 : ‖A + B‖ ≤ c := by rw [hc]; exact norm_add_le A B
    gcongr
  have hVn : ‖V‖ ≤ ρ := by
    rw [hV, hρdef]
    refine le_trans (norm_mul_le _ _) ?_
    have h1 : ‖NormedSpace.exp (scDiv N A)‖ ≤ Real.exp (‖A‖ / N) := by
      refine le_trans (norm_exp_le_exp_norm _) (Real.exp_le_exp.mpr ?_)
      rw [norm_scDiv]
    have h2 : ‖NormedSpace.exp (scDiv N B)‖ ≤ Real.exp (‖B‖ / N) := by
      refine le_trans (norm_exp_le_exp_norm _) (Real.exp_le_exp.mpr ?_)
      rw [norm_scDiv]
    calc ‖NormedSpace.exp (scDiv N A)‖ * ‖NormedSpace.exp (scDiv N B)‖
        ≤ Real.exp (‖A‖ / N) * Real.exp (‖B‖ / N) := by
          exact mul_le_mul h1 h2 (norm_nonneg _) (le_of_lt (Real.exp_pos _))
      _ = Real.exp (c / N) := by
          rw [← Real.exp_add, hc]
          congr 1
          ring
  -- power comparison
  have hpow := pow_diff_norm_le U V ρ hρ1 hUn hVn N
  have hUpow : U ^ N = NormedSpace.exp (A + B) := by
    rw [hU]
    exact exp_scDiv_pow N hN0 (A + B)
  rw [hUpow] at hpow
  have hρN : ρ ^ N = Real.exp c := by
    rw [hρdef, ← Real.exp_nat_mul]
    congr 1
    field_simp
  have hUV := trotter_step A B N hN
  calc ‖NormedSpace.exp (A + B) - V ^ N‖
      ≤ N * ρ ^ N * ‖U - V‖ := hpow
    _ ≤ N * ρ ^ N * (trotterC A B / (N : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hU, hV]
        exact hUV
    _ = Real.exp c * trotterC A B / N := by
        rw [hρN]
        field_simp

end Trotter

/-! ## The Golden–Thompson inequality -/

section GoldenThompsonMain

/-- Lean implementation helper.

Diagonal entries are dominated by the operator norm. -/
lemma norm_diag_entry_le (M : Matrix n n ℂ) (i : n) :
    ‖M i i‖ ≤ ‖M‖ := by
  set e : n → ℂ := Pi.single i (1 : ℂ) with he
  have h1 := norm_dotProduct_mulVec_le M e e
  have h2 : star e ⬝ᵥ (M *ᵥ e) = M i i := by
    rw [he]
    simp [dotProduct, Matrix.mulVec, Pi.single_apply, Pi.star_apply,
      apply_ite (star : ℂ → ℂ)]
  have h3 : l2norm e = 1 := by
    rw [l2norm_eq_sqrt_sum]
    have h4 : ∑ j, ‖e j‖ ^ 2 = 1 := by
      rw [he]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [h4, Real.sqrt_one]
  rw [h2, h3] at h1
  simpa using h1

/-- Lean implementation helper.

The trace is `card n`-Lipschitz for the operator norm (real parts). -/
lemma abs_trace_re_sub_le (X Y : Matrix n n ℂ) :
    |((X.trace).re) - ((Y.trace).re)| ≤
      (Fintype.card n : ℝ) * ‖X - Y‖ := by
  have h1 : (X.trace).re - (Y.trace).re = (((X - Y).trace)).re := by
    rw [Matrix.trace_sub, Complex.sub_re]
  rw [h1]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  calc ‖((X - Y).trace)‖ = ‖∑ i, (X - Y) i i‖ := rfl
    _ ≤ ∑ i, ‖(X - Y) i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, ‖X - Y‖ :=
        Finset.sum_le_sum fun i _ => norm_diag_entry_le (X - Y) i
    _ = (Fintype.card n : ℝ) * ‖X - Y‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Book equation (3.3.3).**

**The Golden–Thompson inequality** (Golden 1965; Thompson 1965):
`tr e^{A+B} ≤ tr(e^A e^B)` for Hermitian `A`, `B`.

Appendix proof (see the module docstring for references): the quantitative
Lie product formula `trotter_bound` along `N = 2^k`, the disentangling
chain `disentangle` (from Dyson's lemma), and passage to the limit. -/
theorem golden_thompson_trace (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((NormedSpace.exp (A + B)).trace).re ≤
      ((NormedSpace.exp A * NormedSpace.exp B).trace).re := by
  set c := ‖A‖ + ‖B‖ with hc
  set L := ((NormedSpace.exp (A + B)).trace).re with hL
  set seq : ℕ → ℝ := fun k =>
    (((NormedSpace.exp (scDiv (2 ^ k) A) *
      NormedSpace.exp (scDiv (2 ^ k) B)) ^ (2 ^ k)).trace).re with hseq
  -- each term of the sequence (k ≥ 1) is dominated by `tr(e^A e^B)`
  have hle : ∀ k : ℕ, 1 ≤ k →
      seq k ≤ ((NormedSpace.exp A * NormedSpace.exp B).trace).re := by
    intro k hk
    set U := NormedSpace.exp (scDiv (2 ^ k) A) with hU
    set V := NormedSpace.exp (scDiv (2 ^ k) B) with hV
    have hUher : U.IsHermitian := (posDef_exp (scDiv_isHermitian hA _)).1
    have hVher : V.IsHermitian := (posDef_exp (scDiv_isHermitian hB _)).1
    have hdis := disentangle k hk U V hUher hVher
    have hUp : U ^ (2 ^ k) = NormedSpace.exp A := by
      rw [hU]
      exact exp_scDiv_pow _ (by positivity) A
    have hVp : V ^ (2 ^ k) = NormedSpace.exp B := by
      rw [hV]
      exact exp_scDiv_pow _ (by positivity) B
    rw [hUp, hVp] at hdis
    have hseqk : seq k = (((U * V) ^ (2 ^ k)).trace).re := rfl
    rw [hseqk]
    exact le_trans (Complex.re_le_norm _) hdis
  -- the sequence converges to `tr e^{A+B}`
  have hbound : ∀ k : ℕ, |seq k - L| ≤
      ((Fintype.card n : ℝ) * (Real.exp c * trotterC A B)) / 2 ^ k := by
    intro k
    have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have ht := trotter_bound A B (2 ^ k) h2k
    have habs := abs_trace_re_sub_le
      ((NormedSpace.exp (scDiv (2 ^ k) A) *
        NormedSpace.exp (scDiv (2 ^ k) B)) ^ (2 ^ k))
      (NormedSpace.exp (A + B))
    have hswap : ‖(NormedSpace.exp (scDiv (2 ^ k) A) *
        NormedSpace.exp (scDiv (2 ^ k) B)) ^ (2 ^ k) -
        NormedSpace.exp (A + B)‖ =
        ‖NormedSpace.exp (A + B) -
        (NormedSpace.exp (scDiv (2 ^ k) A) *
          NormedSpace.exp (scDiv (2 ^ k) B)) ^ (2 ^ k)‖ :=
      norm_sub_rev _ _
    rw [hswap] at habs
    have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    calc |seq k - L|
        ≤ (Fintype.card n : ℝ) *
          ‖NormedSpace.exp (A + B) -
            (NormedSpace.exp (scDiv (2 ^ k) A) *
              NormedSpace.exp (scDiv (2 ^ k) B)) ^ (2 ^ k)‖ := habs
      _ ≤ (Fintype.card n : ℝ) *
          (Real.exp c * trotterC A B / ((2 ^ k : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hc]
          exact ht
      _ = ((Fintype.card n : ℝ) * (Real.exp c * trotterC A B)) / 2 ^ k := by
          rw [hcast]
          ring
  have htend : Filter.Tendsto seq Filter.atTop (nhds L) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (g := fun k => ((Fintype.card n : ℝ) *
      (Real.exp c * trotterC A B)) / 2 ^ k) (fun k => dist_nonneg)
      (fun k => ?_) ?_
    · rw [Real.dist_eq]
      exact hbound k
    · have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      have h2 := h1.const_mul
        ((Fintype.card n : ℝ) * (Real.exp c * trotterC A B))
      rw [mul_zero] at h2
      refine h2.congr fun k => ?_
      rw [one_div, inv_pow, ← div_eq_mul_inv]
  exact le_of_tendsto htend (Filter.eventually_atTop.mpr ⟨1, hle⟩)

end GoldenThompsonMain

end MatrixConcentration
