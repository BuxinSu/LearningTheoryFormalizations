import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher

/-!
# Book Chapter 1 Exercise folder: Section 1.1

Exercises 1.1–1.3 are exercise-local.  The maximum principle from Exercise 1.4
is a Chapter 1 body result and is therefore declared only in the core convexity
module; this leaf deliberately does not duplicate it.  Exercise 1.2 is isolated
here as category A.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace HDP.Chapter1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The convex hull of every set is convex. It is not
consumed by the chapter core or by a later chapter, so its authoritative
declaration remains in this exercise leaf.

**Book Exercise 1.1.** -/
theorem exercise_1_1 (T : Set E) : Convex ℝ (convexHull ℝ T) :=
  convex_convexHull ℝ T

/- EXERCISE-SORRY (category A): Exercise 1.2 is not used by the main line. -/
/-- The pointwise maximum of finitely many convex functions is convex.

`EXERCISE-SORRY`: faithful statement, deliberately deferred because it is non-load-bearing.

**Book Exercise 1.2.** -/
theorem exercise_1_2 {ι : Type*} [Fintype ι] [Nonempty ι] {K : Set E}
    {f : ι → E → ℝ} (hK : Convex ℝ K) (hf : ∀ i, ConvexOn ℝ K (f i)) :
    ConvexOn ℝ K
      (fun x => Finset.univ.sup' Finset.univ_nonempty fun i => f i x) := by
  sorry

/-- Finite Jensen inequality, the substantive content of the source Exercise 1.3(a).
It is exercise-local: neither Chapter 1 core nor a later chapter imports it.

**Book Exercise 1.3(a).** -/
theorem finite_jensen {K : Set E} {f : E → ℝ} (hf : ConvexOn ℝ K f)
    {ι : Type*} {t : Finset ι} {w : ι → ℝ} {x : ι → E}
    (hw0 : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1)
    (hx : ∀ i ∈ t, x i ∈ K) :
    f (∑ i ∈ t, w i • x i) ≤ ∑ i ∈ t, w i * f (x i) := by
  simpa [smul_eq_mul] using hf.map_sum_le hw0 hw1 hx

/-- A function on a convex set is convex if and only if it satisfies Jensen's
inequality for every finite convex combination of points in the set.

**Book Exercise 1.3(a).** -/
theorem convexOn_iff_finite_jensen {K : Set E} (hK : Convex ℝ K) {f : E → ℝ} :
    ConvexOn ℝ K f ↔
      ∀ {ι : Type} (s : Finset ι) (w : ι → ℝ) (x : ι → E),
        (∀ i ∈ s, 0 ≤ w i) → (∑ i ∈ s, w i = 1) →
        (∀ i ∈ s, x i ∈ K) →
        f (∑ i ∈ s, w i • x i) ≤ ∑ i ∈ s, w i * f (x i) := by
  constructor
  · intro hf ι s w x hw0 hw1 hx
    exact finite_jensen hf hw0 hw1 hx
  · intro h
    rw [convexOn_iff hK]
    intro x hx y hy t ht0 ht1
    let w : Fin 2 → ℝ := fun i => if i = 0 then t else 1 - t
    let z : Fin 2 → E := fun i => if i = 0 then x else y
    have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ w i := by
      intro i _
      fin_cases i
      · simpa [w] using ht0
      · simpa [w] using sub_nonneg.mpr ht1
    have hw1 : ∑ i ∈ (Finset.univ : Finset (Fin 2)), w i = 1 := by
      simp [w, Fin.sum_univ_two]
    have hz : ∀ i ∈ (Finset.univ : Finset (Fin 2)), z i ∈ K := by
      intro i _
      fin_cases i
      · simpa [z] using hx
      · simpa [z] using hy
    simpa [w, z, Fin.sum_univ_two] using
      h (ι := Fin 2) (Finset.univ : Finset (Fin 2)) w z hw0 hw1 hz

/-- A convex function evaluated at a finite convex combination is at most the
corresponding weighted sum of its values.

**Book Exercise 1.3(a).** -/
theorem exercise_1_3a {K : Set E} {f : E → ℝ} (hf : ConvexOn ℝ K f)
    {ι : Type*} {t : Finset ι} {w : ι → ℝ} {x : ι → E}
    (hw0 : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1)
    (hx : ∀ i ∈ t, x i ∈ K) :
    f (∑ i ∈ t, w i • x i) ≤ ∑ i ∈ t, w i * f (x i) :=
  finite_jensen hf hw0 hw1 hx

/-- Convexity on a convex set is equivalent to the finite Jensen inequality;
the reverse implication follows by specializing to two points.

**Book Exercise 1.3(a).** -/
theorem exercise_1_3a_iff {K : Set E} (hK : Convex ℝ K) {f : E → ℝ} :
    ConvexOn ℝ K f ↔
      ∀ {ι : Type} (s : Finset ι) (w : ι → ℝ) (x : ι → E),
        (∀ i ∈ s, 0 ≤ w i) → (∑ i ∈ s, w i = 1) →
        (∀ i ∈ s, x i ∈ K) →
        f (∑ i ∈ s, w i • x i) ≤ ∑ i ∈ s, w i * f (x i) :=
  convexOn_iff_finite_jensen hK

/-- Jensen for a finitely-valued random vector.

The finite-range hypothesis records the source's exact exercise setting. The proof uses
the already reconstructed general Jensen theorem, which is stronger and has the same
source-facing conclusion.

**Book Exercise 1.3(b).** -/
theorem exercise_1_3b {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (_hfinite : (Set.range X).Finite) (hf : ConvexOn ℝ Set.univ f)
    (hX : Integrable X μ) (hfX : Integrable (fun ω => f (X ω)) μ) :
    f (∫ ω, X ω ∂μ) ≤ ∫ ω, f (X ω) ∂μ :=
  jensen_inequality_vector hf hX hfX

end HDP.Chapter1
