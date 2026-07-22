import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalLieAlgebra

/-!
# Averaging the column-stabilizer tangent splittings

For the standard subgroup chain on `SO(n)`, fixing a coordinate direction
splits a skew tangent matrix into the rotations involving that coordinate
(the horizontal part) and those avoiding it (the vertical part).  Averaging
over all choices of the fixed coordinate is the mechanism that prevents a
naive subgroup induction from accumulating a harmonic loss.

This file records the exact finite-dimensional bookkeeping.  Every
off-diagonal skew direction belongs to two horizontal summands and to
`n - 2` vertical summands.
-/

open Matrix
open scoped BigOperators

namespace HDP.Appendix.SpecialOrthogonal

/-- Squared Frobenius energy in one row. -/
noncomputable def rowSquareEnergy {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, X i j ^ 2

/-- The horizontal energy for the stabilizer of coordinate `i`.

For a skew matrix this is exactly the squared Frobenius norm of the entries
in row or column `i`: the diagonal entry vanishes and the row and column
energies agree. -/
noncomputable def horizontalSquareEnergy {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  2 * rowSquareEnergy X i

/-- The complementary vertical energy. -/
noncomputable def verticalSquareEnergy {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  HDP.matrixFrobeniusNorm X ^ 2 - horizontalSquareEnergy X i

lemma sum_rowSquareEnergy {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) :
    ∑ i : Fin n, rowSquareEnergy X i =
      HDP.matrixFrobeniusNorm X ^ 2 := by
  rw [HDP.matrixFrobeniusNorm_sq]
  rfl

/-- Each ordered matrix entry occurs in one row, so after skew symmetry is
used to identify row and column energy, every tangent direction occurs in
exactly two horizontal summands. -/
lemma sum_horizontalSquareEnergy {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) :
    ∑ i : Fin n, horizontalSquareEnergy X i =
      2 * HDP.matrixFrobeniusNorm X ^ 2 := by
  simp only [horizontalSquareEnergy, ← Finset.mul_sum]
  rw [sum_rowSquareEnergy]

/-- The complementary vertical summands count every tangent direction
`n - 2` times.  The identity is written over `ℝ`, so it remains total in the
small exceptional dimensions as well. -/
lemma sum_verticalSquareEnergy {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) :
    ∑ i : Fin n, verticalSquareEnergy X i =
      ((n : ℝ) - 2) * HDP.matrixFrobeniusNorm X ^ 2 := by
  rw [show (∑ i : Fin n, verticalSquareEnergy X i) =
      (∑ _i : Fin n, HDP.matrixFrobeniusNorm X ^ 2) -
        ∑ i : Fin n, horizontalSquareEnergy X i by
      simp only [verticalSquareEnergy, Finset.sum_sub_distrib]]
  rw [sum_horizontalSquareEnergy]
  simp
  ring

/-- The sharp scalar recurrence behind the averaged-stabilizer argument.

If the `SO(n-1)` fiber logarithmic-Sobolev coefficient is `a/(n-1)` and the
spherical quotient coefficient is `b/n`, then averaging the `n` splittings
gives the left-hand side below.  The condition `2b ≤ a` closes the induction
at coefficient `a/n`. -/
lemma averaged_stabilizer_coefficient_le
    {n : ℕ} (hn : 2 ≤ n) {a b : ℝ}
    (ha : 0 ≤ a) (hab : 2 * b ≤ a) :
    (a / ((n : ℝ) - 1)) * (((n : ℝ) - 2) / n) +
        (b / n) * (2 / n) ≤
      a / n := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    div_eq_mul_inv, div_eq_mul_inv]
  field_simp [hn0.ne', hn1.ne']
  nlinarith

end HDP.Appendix.SpecialOrthogonal
