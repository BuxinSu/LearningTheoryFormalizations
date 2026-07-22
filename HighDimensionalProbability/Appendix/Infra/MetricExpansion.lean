import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Closed metric expansions

The book defines `A_ε` with an attained witness and a non-strict distance
inequality.  This differs definitionally from both Mathlib's open
`Metric.thickening` and its infimum-distance `Metric.cthickening` for a
nonclosed set, so the Appendix uses the literal source definition.
-/

namespace HDP.Appendix

/-- The source's closed existential `ε`-expansion of a set. -/
def closedExpansion {X : Type*} [PseudoMetricSpace X]
    (ε : ℝ) (A : Set X) : Set X :=
  {x | ∃ y ∈ A, dist x y ≤ ε}

theorem mem_closedExpansion_iff {X : Type*} [PseudoMetricSpace X]
    {ε : ℝ} {A : Set X} {x : X} :
    x ∈ closedExpansion ε A ↔ ∃ y ∈ A, dist x y ≤ ε :=
  Iff.rfl

/-- On a closed set in a proper metric space, the source's attained-witness
expansion agrees with Mathlib's closed thickening. -/
theorem closedExpansion_eq_cthickening {X : Type*} [PseudoMetricSpace X]
    [ProperSpace X] {ε : ℝ} {A : Set X} (hA : IsClosed A) (hε : 0 ≤ ε) :
    closedExpansion ε A = Metric.cthickening ε A := by
  rw [hA.cthickening_eq_biUnion_closedBall hε]
  ext x
  simp only [closedExpansion, Set.mem_setOf_eq, Set.mem_iUnion,
    Metric.mem_closedBall]
  constructor
  · rintro ⟨y, hyA, hxy⟩
    exact ⟨y, ⟨hyA, dist_comm x y ▸ hxy⟩⟩
  · rintro ⟨y, hyA, hyx⟩
    exact ⟨y, hyA, dist_comm y x ▸ hyx⟩

end HDP.Appendix
