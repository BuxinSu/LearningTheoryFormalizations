import MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices
import MatrixConcentration.Appendix_GaussianConcentration
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Logic.Equiv.Bool

/-!
# Appendix: Symmetric lower bound

This module proves **Book equation (6.1.7)** through the following components.

This appendix proves:

* invariance of independent symmetric random matrices under sign flips;
* a deterministic signed-sum averaging inequality;
* the strong constant-one lower bound for symmetric random-matrix sums;
* the book's constant-`1 / 4` lower bound.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Appendix A.8: A lower bound for sums of symmetric random matrices

The proof first factors the joint
law of the independent summands into the product of its marginals.  Symmetry
makes this product law invariant under every deterministic sign pattern.

For deterministic vectors, pair each sign pattern with the pattern obtained
by toggling a coordinate that attains the largest norm.  The elementary
two-point inequality
`2 * ‖x_j‖² ≤ ‖Σ ε_k x_k‖² + ‖Σ ε'_k x_k‖²`
then shows that the largest squared coordinate norm is bounded by the average
of all signed-sum squared norms.  Law invariance makes every term in this
average equal to the original expectation.  This proves the stronger
constant-one inequality; the book's constant `1 / 4` follows immediately.
-/

namespace MatrixConcentration

open Matrix MeasureTheory ProbabilityTheory Finset Set Function
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

section SignFlipLaw

variable {Omega E I : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
  [Fintype I] [DecidableEq I] [Neg E] [MeasurableNeg E]
  {mu : Measure Omega} [IsProbabilityMeasure mu]

/-- Lean implementation helper.

Flip exactly the coordinates selected by a Boolean sign vector. -/
def signFlip (epsilon : I → Bool) (x : I → E) : I → E :=
  fun k => if epsilon k then -x k else x k

/-- Lean implementation helper. -/
private def signFlipMap (epsilon : I → Bool) (k : I) : E → E :=
  if epsilon k then Neg.neg else id

/-- Lean implementation helper. -/
private lemma signFlip_eq (epsilon : I → Bool) :
    signFlip (E := E) epsilon =
      fun x k => signFlipMap (E := E) epsilon k (x k) := by
  funext x k
  simp only [signFlip, signFlipMap]
  split <;> rfl

/-- Lean implementation helper. -/
private lemma measurable_signFlipMap (epsilon : I → Bool) (k : I) :
    Measurable (signFlipMap (E := E) epsilon k) := by
  cases h : epsilon k <;> simp [signFlipMap, h, measurable_neg, measurable_id]

/-- Lean implementation helper. -/
lemma measurable_signFlip (epsilon : I → Bool) :
    Measurable (signFlip (E := E) epsilon) := by
  rw [signFlip_eq]
  exact measurable_pi_lambda _ fun k =>
    (measurable_signFlipMap (E := E) epsilon k).comp (measurable_pi_apply k)

/-- Lean implementation helper.

A finite product of symmetric marginals is invariant under any coordinate
sign pattern. -/
lemma pi_map_signFlip_eq (nu : I → Measure E) [∀ k, IsProbabilityMeasure (nu k)]
    (hneg : ∀ k, nu k = (nu k).map Neg.neg) (epsilon : I → Bool) :
    (Measure.pi nu).map (signFlip (E := E) epsilon) = Measure.pi nu := by
  letI (k : I) : IsProbabilityMeasure
      ((nu k).map (signFlipMap (E := E) epsilon k)) :=
    Measure.isProbabilityMeasure_map
      (measurable_signFlipMap epsilon k).aemeasurable
  rw [signFlip_eq]
  rw [Measure.pi_map_pi fun k =>
    (measurable_signFlipMap epsilon k).aemeasurable]
  congr 1
  funext k
  cases hk : epsilon k
  · simp [signFlipMap, hk]
  · simpa [signFlipMap, hk] using (hneg k).symm

/-- Lean implementation helper.

The joint law of independent symmetric coordinates is invariant under any
deterministic sign pattern. -/
lemma jointLaw_signFlip_invariant {S : I → Omega → E}
    (hind : iIndepFun S mu) (hmeas : ∀ k, Measurable (S k))
    (hsymm : ∀ k, mu.map (S k) = mu.map (fun omega => -(S k omega)))
    (epsilon : I → Bool) :
    mu.map (fun omega => signFlip (E := E) epsilon (fun k => S k omega)) =
      mu.map (fun omega k => S k omega) := by
  letI (k : I) : IsProbabilityMeasure (mu.map (S k)) :=
    Measure.isProbabilityMeasure_map (hmeas k).aemeasurable
  have hneg : ∀ k, mu.map (S k) = (mu.map (S k)).map Neg.neg := by
    intro k
    rw [Measure.map_map measurable_neg (hmeas k)]
    simpa only [Function.comp_def] using hsymm k
  have hPhi : Measurable (fun omega k => S k omega) :=
    measurable_pi_lambda _ hmeas
  calc
    mu.map (fun omega => signFlip (E := E) epsilon (fun k => S k omega)) =
        (mu.map (fun omega k => S k omega)).map
          (signFlip (E := E) epsilon) := by
      rw [Measure.map_map (measurable_signFlip epsilon) hPhi]
      rfl
    _ = (Measure.pi fun k => mu.map (S k)).map
          (signFlip (E := E) epsilon) := by
      rw [hind.map_fun_eq_pi_map fun k => (hmeas k).aemeasurable]
    _ = Measure.pi fun k => mu.map (S k) :=
      pi_map_signFlip_eq _ hneg epsilon
    _ = mu.map (fun omega k => S k omega) :=
      (hind.map_fun_eq_pi_map fun k => (hmeas k).aemeasurable).symm

/-- Lean implementation helper.

Integral transfer through an arbitrary deterministic sign pattern. -/
lemma integral_signFlip_eq_of_symmetric {S : I → Omega → E}
    (hind : iIndepFun S mu) (hmeas : ∀ k, Measurable (S k))
    (hsymm : ∀ k, IsSymmetricRV (S k) mu) (epsilon : I → Bool)
    {F : (I → E) → Real} (hF : Measurable F) :
    (∫ omega, F (signFlip (E := E) epsilon (fun k => S k omega)) ∂mu) =
      ∫ omega, F (fun k => S k omega) ∂mu := by
  have hPhi : Measurable (fun omega k => S k omega) :=
    measurable_pi_lambda _ hmeas
  have hepsilonPhi : Measurable
      (fun omega => signFlip (E := E) epsilon (fun k => S k omega)) :=
    (measurable_signFlip epsilon).comp hPhi
  calc
    (∫ omega, F (signFlip (E := E) epsilon (fun k => S k omega)) ∂mu) =
        ∫ x, F x ∂(mu.map
          (fun omega => signFlip (E := E) epsilon (fun k => S k omega))) :=
      (integral_map hepsilonPhi.aemeasurable
        hF.aestronglyMeasurable).symm
    _ = ∫ x, F x ∂(mu.map (fun omega k => S k omega)) := by
      rw [jointLaw_signFlip_invariant hind hmeas hsymm epsilon]
    _ = ∫ omega, F (fun k => S k omega) ∂mu :=
      integral_map hPhi.aemeasurable hF.aestronglyMeasurable

end SignFlipLaw

section DeterministicSigns

variable {E I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Lean implementation helper.

Toggle the Boolean sign at one coordinate. -/
private def toggleSign (j : I) : (I → Bool) ≃ (I → Bool) :=
  Equiv.piCongrRight fun k => if k = j then Equiv.boolNot else Equiv.refl Bool

/-- Lean implementation helper. -/
private lemma toggleSign_apply (j : I) (epsilon : I → Bool) (k : I) :
    toggleSign j epsilon k = if k = j then !(epsilon k) else epsilon k := by
  by_cases hkj : k = j
  · subst k
    simp [toggleSign]
  · simp [toggleSign, hkj]

/-- Lean implementation helper.

The sum of a finite family with a prescribed Boolean sign pattern. -/
def signedSum (epsilon : I → Bool) (x : I → E) : E :=
  ∑ k, if epsilon k then -x k else x k

/-- Lean implementation helper. -/
private lemma signedSum_toggle (x : I → E) (epsilon : I → Bool) (j : I) :
    signedSum (toggleSign j epsilon) x = signedSum epsilon x -
      2 • (if epsilon j then -x j else x j) := by
  let y : I → E := fun k => if epsilon k then -x k else x k
  have hcoord : ∀ k, (if (toggleSign j epsilon) k then -x k else x k) =
      if k = j then -y k else y k := by
    intro k
    rw [toggleSign_apply]
    by_cases hkj : k = j
    · subst k
      cases hepsilon : epsilon j <;> simp [y, hepsilon]
    · simp [hkj, y]
  simp only [signedSum]
  simp_rw [hcoord]
  have hmem : j ∈ (Finset.univ : Finset I) := Finset.mem_univ j
  rw [← Finset.sum_erase_add _ _ hmem]
  rw [← Finset.sum_erase_add _ _ hmem]
  simp only [ite_true]
  have herase : (∑ k ∈ Finset.univ.erase j, if k = j then -y k else y k) =
      ∑ k ∈ Finset.univ.erase j, y k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [Finset.ne_of_mem_erase hk]
  rw [herase]
  dsimp only [y]
  module

/-- Lean implementation helper. -/
private lemma norm_half_sub_sq_le (a b : E) :
    ‖(1 / 2 : Real) • (a - b)‖ ^ 2 ≤
      (1 / 2 : Real) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hsub := norm_sub_le a b
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2)]
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b),
    sq_nonneg (‖a‖ - ‖b‖)]

/-- Lean implementation helper. -/
private lemma norm_sq_le_pair_signedSum (x : I → E) (epsilon : I → Bool)
    (j : I) :
    2 * ‖x j‖ ^ 2 ≤
      ‖signedSum epsilon x‖ ^ 2 +
        ‖signedSum (toggleSign j epsilon) x‖ ^ 2 := by
  let yj : E := if epsilon j then -x j else x j
  have hyj : yj = (1 / 2 : Real) •
      (signedSum epsilon x - signedSum (toggleSign j epsilon) x) := by
    rw [signedSum_toggle]
    dsimp only [yj]
    module
  have hnorm : ‖yj‖ = ‖x j‖ := by
    dsimp only [yj]
    split <;> simp
  have hhalf := norm_half_sub_sq_le (signedSum epsilon x)
    (signedSum (toggleSign j epsilon) x)
  rw [← hyj, hnorm] at hhalf
  nlinarith

/-- Lean implementation helper.

The largest squared coordinate norm is at most the uniform average of the
squared norms of all signed sums.  The division-free form is convenient for
integration. -/
lemma card_mul_iSup_norm_sq_le_sum_signedSum (x : I → E) :
    (Fintype.card (I → Bool) : Real) * (⨆ j, ‖x j‖ ^ 2) ≤
      ∑ epsilon : I → Bool, ‖signedSum epsilon x‖ ^ 2 := by
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite
    (f := fun j : I => ‖x j‖ ^ 2)
  have hpair : ∀ epsilon : I → Bool,
      2 * (⨆ k, ‖x k‖ ^ 2) ≤
        ‖signedSum epsilon x‖ ^ 2 +
          ‖signedSum (toggleSign j epsilon) x‖ ^ 2 := by
    intro epsilon
    rw [← hj]
    exact norm_sq_le_pair_signedSum x epsilon j
  have hsum := Finset.sum_le_sum
    (fun epsilon (_ : epsilon ∈ (Finset.univ : Finset (I → Bool))) =>
      hpair epsilon)
  have hreindex :
      (∑ epsilon : I → Bool,
        ‖signedSum (toggleSign j epsilon) x‖ ^ 2) =
        ∑ epsilon : I → Bool, ‖signedSum epsilon x‖ ^ 2 :=
    (toggleSign j).sum_comp (fun epsilon => ‖signedSum epsilon x‖ ^ 2)
  rw [Finset.sum_add_distrib, hreindex] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  nlinarith

end DeterministicSigns

section SymmetricLowerBound

variable {Omega I : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
  [IsProbabilityMeasure mu] [Fintype I] [DecidableEq I]
  {d1 d2 : Nat}

/-- Lean implementation helper. -/
private lemma measurable_matrix_family_sum_norm_sq : Measurable
    (fun x : I → Matrix (Fin d1) (Fin d2) Complex => ‖∑ k, x k‖ ^ 2) := by
  fun_prop

/-- Lean implementation helper.

The strong constant-one form of the symmetric-sum lower bound when the
index type is nonempty.

Author note: this is a constant-one strengthening of Book equation (6.1.7), under the same bounded-summand framework used by the registered theorem. -/
theorem symmetric_sum_lower_bound_strong_of_nonempty [Nonempty I]
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) mu)
    {R : I → Real} (h_bdd : ∀ k omega, ‖S k omega‖ ≤ R k) :
    maxSummandSq S mu ≤ ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu := by
  let Cmax : Real := ∑ k, (R k) ^ 2
  let Csum : Real := (∑ k, |R k|) ^ 2
  let qmax : Omega → Real := fun omega => ⨆ k, ‖S k omega‖ ^ 2
  let qsign : (I → Bool) → Omega → Real := fun epsilon omega =>
    ‖signedSum epsilon (fun k => S k omega)‖ ^ 2
  have hqk : ∀ k, Measurable (fun omega => ‖S k omega‖ ^ 2) := fun k =>
    (continuous_l2_opNorm.measurable.comp (h_meas k)).pow_const 2
  have hqmax_meas : Measurable qmax := Measurable.iSup hqk
  have hqmax_nonneg : ∀ omega, 0 ≤ qmax omega := by
    intro omega
    exact (sq_nonneg ‖S (Classical.arbitrary I) omega‖).trans
      (le_ciSup (Finite.bddAbove_range fun k => ‖S k omega‖ ^ 2)
        (Classical.arbitrary I))
  have hqmax_bound : ∀ omega, qmax omega ≤ Cmax := by
    intro omega
    apply ciSup_le
    intro k
    have hk : ‖S k omega‖ ^ 2 ≤ (R k) ^ 2 := by
      nlinarith [norm_nonneg (S k omega), h_bdd k omega]
    exact hk.trans (Finset.single_le_sum (fun i _ => sq_nonneg (R i))
      (Finset.mem_univ k))
  have hqmax_int : Integrable qmax mu := by
    refine Integrable.of_bound hqmax_meas.aestronglyMeasurable Cmax
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hqmax_nonneg omega)]
    exact hqmax_bound omega
  have hsign_meas : ∀ epsilon, Measurable
      (fun omega => signedSum epsilon (fun k => S k omega)) := by
    intro epsilon
    simp only [signedSum]
    apply Finset.measurable_sum
    intro k _
    cases hepsilon : epsilon k
    · simpa [hepsilon] using h_meas k
    · simpa [hepsilon] using (h_meas k).neg
  have hqsign_meas : ∀ epsilon, Measurable (qsign epsilon) := fun epsilon =>
    (continuous_l2_opNorm.measurable.comp (hsign_meas epsilon)).pow_const 2
  have hsigned_bound : ∀ epsilon omega,
      ‖signedSum epsilon (fun k => S k omega)‖ ≤ ∑ k, |R k| := by
    intro epsilon omega
    calc
      ‖signedSum epsilon (fun k => S k omega)‖
          ≤ ∑ k, ‖if epsilon k then -S k omega else S k omega‖ :=
            norm_sum_le _ _
      _ = ∑ k, ‖S k omega‖ := by
        apply Finset.sum_congr rfl
        intro k _
        cases epsilon k <;> simp
      _ ≤ ∑ k, |R k| := by
        apply Finset.sum_le_sum
        intro k _
        exact (h_bdd k omega).trans (le_abs_self (R k))
  have hqsign_int : ∀ epsilon, Integrable (qsign epsilon) mu := by
    intro epsilon
    refine Integrable.of_bound (hqsign_meas epsilon).aestronglyMeasurable Csum
      (Filter.Eventually.of_forall fun omega => ?_)
    have hs := hsigned_bound epsilon omega
    have hsum_nonneg : 0 ≤ ∑ k, |R k| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp only [qsign, Csum]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (signedSum epsilon fun k => S k omega)]
  have hleft_int : Integrable
      (fun omega => (Fintype.card (I → Bool) : Real) * qmax omega) mu :=
    hqmax_int.const_mul _
  have hright_int : Integrable
      (fun omega => ∑ epsilon : I → Bool, qsign epsilon omega) mu :=
    integrable_finsetSum Finset.univ fun epsilon _ => hqsign_int epsilon
  have hpoint : ∀ omega,
      (Fintype.card (I → Bool) : Real) * qmax omega ≤
        ∑ epsilon : I → Bool, qsign epsilon omega := by
    intro omega
    exact card_mul_iSup_norm_sq_le_sum_signedSum (fun k => S k omega)
  have hint := integral_mono hleft_int hright_int hpoint
  have hreflect : ∀ epsilon : I → Bool,
      (∫ omega, qsign epsilon omega ∂mu) =
        ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu := by
    intro epsilon
    simpa only [qsign, signedSum, signFlip] using
      integral_signFlip_eq_of_symmetric h_indep h_meas h_symm epsilon
        (measurable_matrix_family_sum_norm_sq
          (I := I) (d1 := d1) (d2 := d2))
  rw [integral_const_mul] at hint
  rw [integral_finsetSum Finset.univ (fun epsilon _ => hqsign_int epsilon)] at hint
  simp_rw [hreflect] at hint
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hint
  have hcard : 0 < (Fintype.card (I → Bool) : Real) := by positivity
  dsimp only [qmax] at hint
  dsimp only [maxSummandSq]
  nlinarith

/-- Lean implementation helper.

The stronger constant-one lower bound, including the empty-index case.

Author note: this is a constant-one strengthening of Book equation (6.1.7), including the empty-index case. -/
theorem symmetric_sum_lower_bound_strong
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) mu)
    {R : I → Real} (h_bdd : ∀ k omega, ‖S k omega‖ ≤ R k) :
    maxSummandSq S mu ≤ ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hempty =>
      letI := hempty
      simp [maxSummandSq]
  | inr hnonempty =>
      letI := hnonempty
      exact symmetric_sum_lower_bound_strong_of_nonempty
        h_indep h_meas h_symm h_bdd

/-- Lean implementation helper. -/
private lemma maxSummandSq_nonneg_finite
    (S : I → Omega → Matrix (Fin d1) (Fin d2) Complex) :
    0 ≤ maxSummandSq S mu := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hempty =>
      letI := hempty
      simp [maxSummandSq]
  | inr hnonempty =>
      letI := hnonempty
      rw [maxSummandSq]
      exact integral_nonneg fun omega =>
        (sq_nonneg ‖S (Classical.arbitrary I) omega‖).trans
          (le_ciSup (Finite.bddAbove_range fun k => ‖S k omega‖ ^ 2)
            (Classical.arbitrary I))

/-- Lean implementation helper.

Derives Book equation (6.1.7) from the stronger constant-one estimate.

Author note: this helper yields the book’s `1/4` constant from the stronger constant-one estimate. -/
theorem symmetric_sum_lower_bound_aux
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) mu)
    {R : I → Real} (h_bdd : ∀ k omega, ‖S k omega‖ ≤ R k) :
    (1 / 4 : Real) * maxSummandSq S mu ≤
      ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu := by
  calc
    (1 / 4 : Real) * maxSummandSq S mu ≤ 1 * maxSummandSq S mu :=
      mul_le_mul_of_nonneg_right (by norm_num) (maxSummandSq_nonneg_finite S)
    _ = maxSummandSq S mu := one_mul _
    _ ≤ ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu :=
      symmetric_sum_lower_bound_strong h_indep h_meas h_symm h_bdd

/-! The next two declarations remove the bounded-summand convenience
assumption.  The single hypothesis that the pointwise maximum squared norm is
integrable dominates every signed sum (there are only finitely many
coordinates), so the same finite sign-averaging argument applies verbatim. -/

/-- Lean implementation helper.

The constant-one symmetric-sum lower bound under the book's natural finite
second-maximum assumption. -/
theorem symmetric_sum_lower_bound_strong_integrable
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) mu)
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    maxSummandSq S mu ≤ ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hempty =>
      letI := hempty
      simp [maxSummandSq]
  | inr hnonempty =>
      letI := hnonempty
      let qmax : Omega → Real := fun omega => ⨆ k, ‖S k omega‖ ^ 2
      let qsign : (I → Bool) → Omega → Real := fun epsilon omega =>
        ‖signedSum epsilon (fun k => S k omega)‖ ^ 2
      have hqmax_nonneg : ∀ omega, 0 ≤ qmax omega := by
        intro omega
        exact (sq_nonneg ‖S (Classical.arbitrary I) omega‖).trans
          (le_ciSup (Finite.bddAbove_range fun k => ‖S k omega‖ ^ 2)
            (Classical.arbitrary I))
      have hsign_meas : ∀ epsilon, Measurable
          (fun omega => signedSum epsilon (fun k => S k omega)) := by
        intro epsilon
        simp only [signedSum]
        apply Finset.measurable_sum
        intro k _
        cases hepsilon : epsilon k
        · simpa [hepsilon] using h_meas k
        · simpa [hepsilon] using (h_meas k).neg
      have hqsign_meas : ∀ epsilon, Measurable (qsign epsilon) := fun epsilon =>
        (continuous_l2_opNorm.measurable.comp (hsign_meas epsilon)).pow_const 2
      have hqsign_bound : ∀ epsilon omega,
          qsign epsilon omega ≤ (Fintype.card I : Real) ^ 2 * qmax omega := by
        intro epsilon omega
        have hsum : ‖signedSum epsilon (fun k => S k omega)‖ ≤
            ∑ k, ‖S k omega‖ := by
          calc
            ‖signedSum epsilon (fun k => S k omega)‖ ≤
                ∑ k, ‖if epsilon k then -S k omega else S k omega‖ :=
              norm_sum_le _ _
            _ = ∑ k, ‖S k omega‖ := by
              apply Finset.sum_congr rfl
              intro k _
              cases epsilon k <;> simp
        have hsquares : (∑ k, ‖S k omega‖) ^ 2 ≤
            (Fintype.card I : Real) * ∑ k, ‖S k omega‖ ^ 2 := by
          simpa using (sq_sum_le_card_mul_sum_sq
            (s := (Finset.univ : Finset I)) (f := fun k => ‖S k omega‖))
        have hterms : (∑ k, ‖S k omega‖ ^ 2) ≤
            (Fintype.card I : Real) * qmax omega := by
          calc
            (∑ k, ‖S k omega‖ ^ 2) ≤ ∑ _k : I, qmax omega := by
              exact Finset.sum_le_sum fun k _ =>
                le_ciSup (Finite.bddAbove_range fun j => ‖S j omega‖ ^ 2) k
            _ = (Fintype.card I : Real) * qmax omega := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp only [qsign]
        have hsum0 : 0 ≤ ∑ k, ‖S k omega‖ :=
          Finset.sum_nonneg fun k (_ : k ∈ (Finset.univ : Finset I)) =>
            norm_nonneg (S k omega)
        have hsigned_sq : ‖signedSum epsilon (fun k => S k omega)‖ ^ 2 ≤
            (∑ k, ‖S k omega‖) ^ 2 := by
          nlinarith [norm_nonneg (signedSum epsilon fun k => S k omega),
            hsum0]
        calc
          ‖signedSum epsilon (fun k => S k omega)‖ ^ 2 ≤
              (∑ k, ‖S k omega‖) ^ 2 := hsigned_sq
          _ ≤ (Fintype.card I : Real) * ∑ k, ‖S k omega‖ ^ 2 := hsquares
          _ ≤ (Fintype.card I : Real) *
              ((Fintype.card I : Real) * qmax omega) :=
            mul_le_mul_of_nonneg_left hterms (Nat.cast_nonneg _)
          _ = (Fintype.card I : Real) ^ 2 * qmax omega := by ring
      have hqsign_int : ∀ epsilon, Integrable (qsign epsilon) mu := by
        intro epsilon
        refine (hM.const_mul ((Fintype.card I : Real) ^ 2)).mono'
          (hqsign_meas epsilon).aestronglyMeasurable
          (Filter.Eventually.of_forall fun omega => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simpa only [qmax] using hqsign_bound epsilon omega
      have hleft_int : Integrable
          (fun omega => (Fintype.card (I → Bool) : Real) * qmax omega) mu :=
        (by simpa only [qmax] using hM.const_mul (Fintype.card (I → Bool) : Real))
      have hright_int : Integrable
          (fun omega => ∑ epsilon : I → Bool, qsign epsilon omega) mu :=
        integrable_finsetSum Finset.univ fun epsilon _ => hqsign_int epsilon
      have hpoint : ∀ omega,
          (Fintype.card (I → Bool) : Real) * qmax omega ≤
            ∑ epsilon : I → Bool, qsign epsilon omega := by
        intro omega
        exact card_mul_iSup_norm_sq_le_sum_signedSum (fun k => S k omega)
      have hint := integral_mono hleft_int hright_int hpoint
      have hreflect : ∀ epsilon : I → Bool,
          (∫ omega, qsign epsilon omega ∂mu) =
            ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu := by
        intro epsilon
        simpa only [qsign, signedSum, signFlip] using
          integral_signFlip_eq_of_symmetric h_indep h_meas h_symm epsilon
            (measurable_matrix_family_sum_norm_sq
              (I := I) (d1 := d1) (d2 := d2))
      rw [integral_const_mul] at hint
      rw [integral_finsetSum Finset.univ (fun epsilon _ => hqsign_int epsilon)] at hint
      simp_rw [hreflect] at hint
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hint
      have hcard : 0 < (Fintype.card (I → Bool) : Real) := by positivity
      dsimp only [qmax] at hint
      dsimp only [maxSummandSq]
      nlinarith

/-- **Book equation (6.1.7)** under the minimal finite expected maximum-square
hypothesis.  This is the integrable counterpart of the bounded
`symmetric_sum_lower_bound`; in fact the proof establishes the stronger
constant-one bound before retaining the Book's `1/4` conclusion. -/
theorem symmetric_sum_lower_bound_integrable
    {S : I → Omega → Matrix (Fin d1) (Fin d2) Complex}
    (h_indep : iIndepFun S mu) (h_meas : ∀ k, Measurable (S k))
    (h_symm : ∀ k, IsSymmetricRV (S k) mu)
    (hM : Integrable (fun omega => ⨆ k, ‖S k omega‖ ^ 2) mu) :
    (1 / 4 : Real) * maxSummandSq S mu ≤
      ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu := by
  calc
    (1 / 4 : Real) * maxSummandSq S mu ≤ 1 * maxSummandSq S mu :=
      mul_le_mul_of_nonneg_right (by norm_num) (maxSummandSq_nonneg_finite S)
    _ = maxSummandSq S mu := one_mul _
    _ ≤ ∫ omega, ‖∑ k, S k omega‖ ^ 2 ∂mu :=
      symmetric_sum_lower_bound_strong_integrable h_indep h_meas h_symm hM

end SymmetricLowerBound

end MatrixConcentration
