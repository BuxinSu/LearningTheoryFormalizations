import HighDimensionalProbability.Appendix.Infra.Concentration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.UniformOn
import Mathlib.GroupTheory.Perm.Fin

/-!
# Independent-digit model of a uniform finite permutation

This file implements the Fisher--Yates (or insertion) code used in the proof
of symmetric-group concentration.  A permutation of `Fin n` is encoded by
independent digits `x i : Fin (i + 1)`.  Mathlib's
`Equiv.Perm.decomposeFin` supplies the recursive bijection.

The key deterministic estimate is that changing one digit changes at most
three values of the decoded permutation.  The constant three is sharp for
this particular insertion code: at the outermost step, changing the selected
value replaces one transposition by another, whose quotient is supported on
at most three points.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace HDP.Chapter5.Appendix.SymmetricCode

noncomputable section

/-- Independent insertion digits for a permutation of `Fin n`. -/
abbrev PermutationCode (n : Nat) : Type :=
  forall i : Fin n, Fin (i.1 + 1)

instance (n : Nat) : Fintype (PermutationCode n) := inferInstance

instance (n : Nat) : Nonempty (PermutationCode n) := by
  unfold PermutationCode
  infer_instance

/-- Separate the last (outermost) insertion digit. -/
def codeDecompose (n : Nat) :
    PermutationCode (n + 1) ≃ Fin (n + 1) × PermutationCode n where
  toFun x :=
    (x (Fin.last n), fun i => x i.castSucc)
  invFun x := fun i => Fin.lastCases x.1 x.2 i
  left_inv x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv x := by
    apply Prod.ext
    · simp
    · funext i
      simp

/-- The recursive Fisher--Yates code is a bijection onto all permutations. -/
def permutationCodeEquiv : forall n : Nat,
    PermutationCode n ≃ Equiv.Perm (Fin n)
  | 0 => Equiv.ofUnique (PermutationCode 0) (Equiv.Perm (Fin 0))
  | n + 1 =>
      (codeDecompose n).trans
        ((Equiv.refl (Fin (n + 1))).prodCongr (permutationCodeEquiv n) |>.trans
          Equiv.Perm.decomposeFin.symm)

/-- Product law of the independent insertion digits. -/
def codeMeasure (n : Nat) : Measure (PermutationCode n) :=
  Measure.pi (fun i : Fin n => uniformOn (Set.univ : Set (Fin (i.1 + 1))))

instance (n : Nat) : IsProbabilityMeasure (codeMeasure n) := by
  unfold codeMeasure
  infer_instance

/-- The product digit law is the uniform law on the finite code space. -/
lemma codeMeasure_eq_uniform (n : Nat) :
    codeMeasure n = uniformOn (Set.univ : Set (PermutationCode n)) := by
  apply Measure.ext_of_singleton
  intro x
  rw [codeMeasure, Measure.pi_singleton]
  simp only [uniformOn_univ]
  rw [Fintype.card_pi]
  simp only [Measure.count_singleton, one_div]
  push_cast
  symm
  apply ENNReal.prod_inv_distrib
  intro i hi j hj hij
  left
  simp

/-- Number of inputs on which two permutations disagree. -/
def disagreementCount {n : Nat} (s t : Equiv.Perm (Fin n)) : Nat :=
  (Finset.univ.filter fun i => s i ≠ t i).card

lemma disagreementCount_eq_sum {n : Nat} (s t : Equiv.Perm (Fin n)) :
    disagreementCount s t = ∑ i, if s i ≠ t i then 1 else 0 := by
  symm
  simpa [disagreementCount] using
    (Finset.sum_boole (R := Nat) (fun i : Fin n => s i ≠ t i) Finset.univ)

lemma decompose_eq_swap_mul_lift {n : Nat} (p : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (p, e) =
      Equiv.swap 0 p * Equiv.Perm.decomposeFin.symm (0, e) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Changing the outer insertion digit changes at most three images. -/
lemma disagreementCount_decompose_same_tail_le_three {n : Nat}
    (p q : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    disagreementCount (Equiv.Perm.decomposeFin.symm (p, e))
      (Equiv.Perm.decomposeFin.symm (q, e)) <= 3 := by
  let L : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm (0, e)
  let D : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun i =>
      Equiv.Perm.decomposeFin.symm (p, e) i ≠
        Equiv.Perm.decomposeFin.symm (q, e) i
  let T : Finset (Fin (n + 1)) := {0, p, q}
  have hsub : D.map L.toEmbedding <= T := by
    intro y hy
    rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [T, Finset.mem_insert, Finset.mem_singleton]
    by_contra h
    push Not at h
    have hpfix : Equiv.swap 0 p (L x) = L x :=
      Equiv.swap_apply_of_ne_of_ne h.1 h.2.1
    have hqfix : Equiv.swap 0 q (L x) = L x :=
      Equiv.swap_apply_of_ne_of_ne h.1 h.2.2
    have hpform : Equiv.Perm.decomposeFin.symm (p, e) x =
        Equiv.swap 0 p (L x) := by
      rw [decompose_eq_swap_mul_lift]
      simp [L]
    have hqform : Equiv.Perm.decomposeFin.symm (q, e) x =
        Equiv.swap 0 q (L x) := by
      rw [decompose_eq_swap_mul_lift]
      simp [L]
    apply hx
    rw [hpform, hqform, hpfix, hqfix]
  calc
    disagreementCount (Equiv.Perm.decomposeFin.symm (p, e))
        (Equiv.Perm.decomposeFin.symm (q, e)) = D.card := rfl
    _ = (D.map L.toEmbedding).card := (Finset.card_map _).symm
    _ <= T.card := Finset.card_le_card hsub
    _ <= 3 := by
      calc
        ({0, p, q} : Finset (Fin (n + 1))).card ≤
            ({p, q} : Finset (Fin (n + 1))).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ ({q} : Finset (Fin (n + 1))).card + 1 + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) 1
        _ = 3 := by simp

/-- With the outer digit fixed, disagreement is exactly disagreement of the
recursively decoded tail. -/
lemma disagreementCount_decompose_same_head {n : Nat}
    (p : Fin (n + 1)) (e e' : Equiv.Perm (Fin n)) :
    disagreementCount (Equiv.Perm.decomposeFin.symm (p, e))
      (Equiv.Perm.decomposeFin.symm (p, e')) = disagreementCount e e' := by
  rw [disagreementCount_eq_sum, disagreementCount_eq_sum]
  rw [Fin.sum_univ_succ]
  simp

@[simp]
lemma permutationCodeEquiv_apply_succ (n : Nat) (x : PermutationCode (n + 1)) :
    permutationCodeEquiv (n + 1) x =
      Equiv.Perm.decomposeFin.symm
        (x (Fin.last n), permutationCodeEquiv n (fun i => x i.castSucc)) := rfl

/-- Every one-coordinate change of the independent code changes at most
three values of the decoded permutation. -/
lemma disagreementCount_permutationCodeEquiv_le_three :
    forall (n : Nat) (x y : PermutationCode n) (i : Fin n),
      (forall j, j ≠ i -> x j = y j) ->
      disagreementCount (permutationCodeEquiv n x)
        (permutationCodeEquiv n y) <= 3 := by
  intro n
  induction n with
  | zero =>
      intro x y i
      exact Fin.elim0 i
  | succ n ih =>
      intro x y i hxy
      induction i using Fin.lastCases with
      | last =>
        let tx : PermutationCode n := fun j => x j.castSucc
        let ty : PermutationCode n := fun j => y j.castSucc
        have ht : tx = ty := by
          funext j
          apply hxy j.castSucc
          simp
        rw [permutationCodeEquiv_apply_succ, permutationCodeEquiv_apply_succ]
        simpa [tx, ty, ht] using
          disagreementCount_decompose_same_tail_le_three
            (x (Fin.last n)) (y (Fin.last n)) (permutationCodeEquiv n tx)
      | cast k =>
        let tx : PermutationCode n := fun j => x j.castSucc
        let ty : PermutationCode n := fun j => y j.castSucc
        have hhead : x (Fin.last n) = y (Fin.last n) := by
          apply hxy
          exact (Fin.castSucc_ne_last k).symm
        rw [permutationCodeEquiv_apply_succ, permutationCodeEquiv_apply_succ, hhead]
        change disagreementCount
          (Equiv.Perm.decomposeFin.symm
            (y (Fin.last n), permutationCodeEquiv n tx))
          (Equiv.Perm.decomposeFin.symm
            (y (Fin.last n), permutationCodeEquiv n ty)) ≤ 3
        rw [disagreementCount_decompose_same_head]
        apply ih tx ty k
        intro j hj
        change x j.castSucc = y j.castSucc
        apply hxy j.castSucc
        intro hji
        apply hj
        exact Fin.castSucc_injective n hji

/-- Measurable version of the finite Fisher--Yates equivalence. -/
local instance permutationMeasurableSpace (n : Nat) :
    MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- The finite permutation-code equivalence as an equivalence of measurable spaces. -/
def permutationCodeMeasurableEquiv (n : Nat) :
    PermutationCode n ≃ᵐ Equiv.Perm (Fin n) where
  toEquiv := permutationCodeEquiv n
  measurable_toFun := measurable_of_finite _
  measurable_invFun := measurable_of_finite _

/-- Decoding independent uniform digits gives the uniform permutation law. -/
lemma map_codeMeasure_permutationCodeEquiv (n : Nat) :
    Measure.map (permutationCodeMeasurableEquiv n) (codeMeasure n) =
      uniformOn (Set.univ : Set (Equiv.Perm (Fin n))) := by
  rw [codeMeasure_eq_uniform]
  apply Measure.ext_of_singleton
  intro s
  rw [Measure.map_apply (permutationCodeMeasurableEquiv n).measurable
    (MeasurableSet.singleton s)]
  have hpre : (permutationCodeMeasurableEquiv n) ⁻¹' {s} =
      {(permutationCodeEquiv n).symm s} := by
    ext x
    change permutationCodeEquiv n x = s ↔ x = (permutationCodeEquiv n).symm s
    exact (permutationCodeEquiv n).apply_eq_iff_eq_symm_apply
  rw [hpre]
  rw [uniformOn_univ, uniformOn_univ]
  simp only [Measure.count_singleton]
  rw [Fintype.card_congr (permutationCodeEquiv n)]

/-- The Fisher--Yates decoder is measure preserving. -/
def permutationCodeMeasurePreserving (n : Nat) :
    MeasurePreserving (permutationCodeMeasurableEquiv n) (codeMeasure n)
      (uniformOn (Set.univ : Set (Equiv.Perm (Fin n)))) :=
  ⟨(permutationCodeMeasurableEquiv n).measurable,
    map_codeMeasure_permutationCodeEquiv n⟩

end

end HDP.Chapter5.Appendix.SymmetricCode
