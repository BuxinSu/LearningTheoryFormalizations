import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Shared finite simple-graph cut infrastructure
-/

open scoped BigOperators

namespace HDP

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- The number of edges crossing the cut `s | sᶜ`.

**Book Definition 3.6.1.** -/
noncomputable def cutSize (G : _root_.SimpleGraph V) (s : Set V) : ℕ := by
  classical
  exact (G.between s sᶜ).edgeFinset.card

/-- The real-valued cut objective used by Chapter 3.

**Book Definition 3.6.1.** -/
noncomputable def cutValue (G : _root_.SimpleGraph V) (s : Set V) : ℝ :=
  cutSize G s

/-- Maximum cut size, as a finite supremum over vertex subsets.

**Book Definition 3.6.1.** -/
noncomputable def maxCutSize (G : _root_.SimpleGraph V) : ℕ := by
  classical
  exact Finset.univ.sup fun s : Finset V => cutSize G (s : Set V)

/-- Cut size and maximum cut of a finite graph.

**Book Definition 3.6.1.** -/
noncomputable def maxCutValue (G : _root_.SimpleGraph V) : ℝ :=
  maxCutSize G

/-- Bounds `cutSize` above by `maxCutSize`.

**Lean implementation helper.** -/
theorem cutSize_le_maxCutSize (G : _root_.SimpleGraph V) (s : Finset V) :
    cutSize G (s : Set V) ≤ maxCutSize G := by
  classical
  exact Finset.le_sup (s := (Finset.univ : Finset (Finset V)))
    (f := fun t : Finset V => cutSize G (t : Set V)) (Finset.mem_univ s)

/-- Bounds `cutValue` above by `maxCutValue`.

**Lean implementation helper.** -/
theorem cutValue_le_maxCutValue (G : _root_.SimpleGraph V) (s : Finset V) :
    cutValue G (s : Set V) ≤ maxCutValue G := by
  change (cutSize G (s : Set V) : ℝ) ≤ (maxCutSize G : ℝ)
  exact_mod_cast cutSize_le_maxCutSize G s

end SimpleGraph

end HDP
