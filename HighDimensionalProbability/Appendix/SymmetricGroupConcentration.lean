import HighDimensionalProbability.Appendix.BoundedDifferences
import HighDimensionalProbability.Appendix.Infra.SymmetricGroupCode

/-!
# HDP Theorem 5.2.6: concentration on the symmetric group

This reconstructs the martingale/bounded-differences proof suggested in the
source notes.  We realize a uniform permutation by independent Fisher--Yates
insertion digits.  Changing one digit changes at most three values of the
decoded permutation, so McDiarmid's inequality gives the claimed
`O(n⁻¹ᐟ²)` concentration scale.  The proof below exposes the explicit
absolute constant `C = 3/2`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace HDP.Chapter5

noncomputable section

/-- Normalized Hamming distance on permutations. -/
noncomputable def permutationHammingDistance {n : Nat}
    (s t : Equiv.Perm (Fin n)) : Real :=
  ((Finset.univ.filter fun i => s i ≠ t i).card : Real) / n

namespace Appendix

/-- Exact McDiarmid parameter for `n` coordinate bounds equal to `3/n`. -/
lemma symmetricParameter_three_div (n : Nat) (hn : 0 < n) :
    ((boundedDifferencesParameter
      (fun _ : Fin n => 3 / (n : Real)) : ℝ≥0) : Real) =
      ((3 / 2 : Real) / Real.sqrt n) ^ 2 := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : Real) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
  simp only [boundedDifferencesParameter, Fin.sum_const, nsmul_eq_mul]
  push_cast
  rw [oscillationParameter, Real.coe_toNNReal _ (by positivity)]
  field_simp [hsqrt, ne_of_gt hnR]
  nlinarith [Real.sq_sqrt hnR.le]

end Appendix

/-- **HDP Theorem 5.2.6 (symmetric-group concentration).**

The uniform law on `Perm (Fin n)`, equipped with normalized Hamming distance,
has mean-centered Gaussian concentration at scale `3 / (2 * sqrt n)`. -/
theorem symmetric_group_concentration :
    ∃ C : Real, 0 < C ∧ ∀ (n : Nat), 0 < n →
      letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
      HasMeanConcentration
        (uniformOn (Set.univ : Set (Equiv.Perm (Fin n))))
        permutationHammingDistance (C / Real.sqrt n) := by
  refine ⟨3 / 2, by norm_num, ?_⟩
  intro n hn
  letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  intro f hf hlip hfint t ht
  let E := Appendix.SymmetricCode.permutationCodeMeasurableEquiv n
  let mp := Appendix.SymmetricCode.permutationCodeMeasurePreserving n
  let g : Appendix.SymmetricCode.PermutationCode n -> Real := fun x => f (E x)
  have hg : Measurable g := hf.comp E.measurable
  have hgint : Integrable g (Appendix.SymmetricCode.codeMeasure n) := by
    exact mp.integrable_comp_of_integrable hfint
  have hcoord : forall x y (i : Fin n),
      (forall j, j ≠ i -> x j = y j) ->
      |g x - g y| <= 3 / (n : Real) := by
    intro x y i hxy
    calc
      |g x - g y| <= permutationHammingDistance (E x) (E y) := hlip _ _
      _ <= 3 / (n : Real) := by
        change ((Appendix.SymmetricCode.disagreementCount (E x) (E y) : Nat) : Real) /
            (n : Real) <= 3 / (n : Real)
        have hc :=
          Appendix.SymmetricCode.disagreementCount_permutationCodeEquiv_le_three
            n x y i hxy
        have hnR : (0 : Real) < n := by exact_mod_cast hn
        gcongr
        exact_mod_cast hc
  have hmgf := Appendix.boundedDifferences_hasSubgaussianMGF
    (mu := fun i : Fin n => uniformOn (Set.univ : Set (Fin (i.1 + 1))))
    (f := g) (c := fun _ : Fin n => 3 / (n : Real))
    hg (fun _ => by positivity) hcoord hgint
  change HasSubgaussianMGF
    (fun x => g x - ∫ y, g y ∂(Appendix.SymmetricCode.codeMeasure n))
    (Appendix.boundedDifferencesParameter
      (fun _ : Fin n => 3 / (n : Real)))
    (Appendix.SymmetricCode.codeMeasure n) at hmgf
  have htail := Appendix.twoSidedTail_of_hasSubgaussianMGF
    (Appendix.SymmetricCode.codeMeasure n)
    (fun x => g x - ∫ y, g y ∂(Appendix.SymmetricCode.codeMeasure n))
    (Appendix.boundedDifferencesParameter
      (fun _ : Fin n => 3 / (n : Real))) hmgf t ht
  rw [Appendix.symmetricParameter_three_div n hn] at htail
  have hmean :
      (∫ x, g x ∂(Appendix.SymmetricCode.codeMeasure n)) =
        ∫ s, f s ∂(uniformOn (Set.univ : Set (Equiv.Perm (Fin n)))) := by
    exact mp.integral_comp' f
  let S : Set (Equiv.Perm (Fin n)) :=
    {s | t <= |f s -
      ∫ u, f u ∂(uniformOn (Set.univ : Set (Equiv.Perm (Fin n))))|}
  have hS : MeasurableSet S := by
    change S ∈ (⊤ : Set (Set (Equiv.Perm (Fin n))))
    simp
  have hmeasure :
      (Appendix.SymmetricCode.codeMeasure n).real (E ⁻¹' S) =
        (uniformOn (Set.univ : Set (Equiv.Perm (Fin n)))).real S := by
    rw [measureReal_def, measureReal_def]
    congr 1
    rw [← mp.map_eq, Measure.map_apply E.measurable hS]
  rw [← hmeasure]
  simpa only [S, g, Set.preimage_setOf_eq, hmean] using htail

end

end HDP.Chapter5
