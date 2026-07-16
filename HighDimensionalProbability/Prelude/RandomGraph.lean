import HighDimensionalProbability.Prelude.Basic
import Mathlib.Data.Sym.Card
import Mathlib.MeasureTheory.Integral.Pi

/-!
# A finite Erdős–Rényi edge model

This module supplies the book-wide finite product-space model used by Chapters 1 and 2.
The sample space has one independent Bernoulli coordinate for every off-diagonal unordered
pair of vertices.  Thus no loop coordinates or duplicate oriented edges are present.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal unitInterval

namespace HDP

/-- The off-diagonal unordered edges on `Fin n`. -/
abbrev EREdge (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- The finite sample space of edge-presence assignments. -/
abbrev ERSample (n : ℕ) := EREdge n → Bool

/-- The vertices other than a fixed vertex `v`. -/
abbrev ERNeighbor (n : ℕ) (v : Fin n) := {w : Fin n // w ≠ v}

/-- The finite Erdős–Rényi product measure `G(n,p)`.

**Lean implementation helper.** -/
noncomputable def erdosRenyi (n : ℕ) (p : I) : Measure (ERSample n) :=
  Measure.pi fun _ : EREdge n ↦ bernoulliMeasure true false p

noncomputable instance erdosRenyi.isProbabilityMeasure {n : ℕ} {p : I} :
    IsProbabilityMeasure (erdosRenyi n p) := by
  rw [erdosRenyi]
  infer_instance

/-- The edge between `v` and a distinct vertex `w`.

**Lean implementation helper.** -/
def incidentEdge {n : ℕ} (v : Fin n) (w : ERNeighbor n v) : EREdge n :=
  ⟨s(v, w.1), by simpa using w.2.symm⟩

/-- The real-valued indicator of an edge.

**Lean implementation helper.** -/
def edgeIndicator {n : ℕ} (e : EREdge n) (G : ERSample n) : ℝ :=
  if G e then 1 else 0

/-- The real-valued degree of a vertex, obtained by summing its incident-edge indicators.

**Lean implementation helper.** -/
def degree {n : ℕ} (v : Fin n) (G : ERSample n) : ℝ :=
  ∑ w : ERNeighbor n v, edgeIndicator (incidentEdge v w) G

/-- The expected degree `(n-1)p`.

**Lean implementation helper.** -/
def expectedDegree (n : ℕ) (p : I) : ℝ := (n - 1 : ℕ) * (p : ℝ)

/-- Each vertex in an `n`-vertex loopless graph has exactly `n - 1` possible neighbors.

**Lean implementation helper.** -/
@[simp]
lemma card_erNeighbor {n : ℕ} (v : Fin n) : Fintype.card (ERNeighbor n v) = n - 1 := by
  simp [ERNeighbor]

/-- Each edge coordinate has law `Ber(p)`.

**Lean implementation helper.** -/
lemma edgeIndicator_isBernoulli {n : ℕ} (p : I) (e : EREdge n) :
    HDP.IsBernoulli (edgeIndicator e) p (erdosRenyi n p) := by
  refine ⟨by fun_prop, ?_⟩
  change Measure.map ((fun b : Bool ↦ if b then (1 : ℝ) else 0) ∘ fun G ↦ G e)
      (Measure.pi fun _ : EREdge n ↦ bernoulliMeasure true false p) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), Measure.pi_map_eval]
  convert map_bernoulliMeasure true false
    (fun b : Bool ↦ if b then (1 : ℝ) else 0) p using 1 <;> simp

/-- The probability that a fixed edge is absent is `1-p`.

**Lean implementation helper.** -/
lemma edge_absent_probability {n : ℕ} (p : I) (e : EREdge n) :
    (erdosRenyi n p).real (edgeIndicator e ⁻¹' {0}) = 1 - (p : ℝ) := by
  let h := edgeIndicator_isBernoulli p e
  calc
    (erdosRenyi n p).real (edgeIndicator e ⁻¹' {0})
        = ((erdosRenyi n p).map (edgeIndicator e)).real {0} := by
          rw [measureReal_def, measureReal_def,
            Measure.map_apply_of_aemeasurable h.aemeasurable (by measurability)]
    _ = (bernoulliMeasure (1 : ℝ) 0 p).real {0} := by rw [h.map_eq]
    _ = 1 - (p : ℝ) := by
      rw [bernoulliMeasure_real_apply p (by measurability)]
      simp

/-- The full family of edge indicators is independent.

**Lean implementation helper.** -/
lemma edgeIndicator_independent {n : ℕ} (p : I) :
    iIndepFun (fun e : EREdge n ↦ edgeIndicator e) (erdosRenyi n p) := by
  change iIndepFun (fun e : EREdge n ↦ fun G ↦ if G e then (1 : ℝ) else 0)
    (Measure.pi fun _ : EREdge n ↦ bernoulliMeasure true false p)
  have h := iIndepFun_pi
    (X := fun _ : EREdge n ↦ fun b : Bool ↦ if b then (1 : ℝ) else 0)
    (μ := fun _ : EREdge n ↦ bernoulliMeasure true false p) (fun _ ↦ by fun_prop)
  exact h

/-- For a fixed vertex, distinct neighboring vertices determine distinct incident edges.

**Lean implementation helper.** -/
lemma incidentEdge_injective {n : ℕ} (v : Fin n) :
    Function.Injective (incidentEdge v) := by
  intro w z hwz
  apply Subtype.ext
  exact (Sym2.mkEmbedding v).injective (congrArg Subtype.val hwz)

/-- The `n-1` indicators incident to a fixed vertex are independent.

**Lean implementation helper.** -/
lemma incident_independent {n : ℕ} (p : I) (v : Fin n) :
    iIndepFun (fun w : ERNeighbor n v ↦ edgeIndicator (incidentEdge v w))
      (erdosRenyi n p) := by
  exact iIndepFun.precomp (incidentEdge_injective v) (edgeIndicator_independent p)

/-- The expected degree of every vertex is `(n-1)p`.

**Lean implementation helper.** -/
theorem degree_expectation {n : ℕ} (p : I) (v : Fin n) :
    ∫ G, degree v G ∂(erdosRenyi n p) = expectedDegree n p := by
  change (∫ G, ∑ w : ERNeighbor n v, edgeIndicator (incidentEdge v w) G
    ∂(erdosRenyi n p)) = expectedDegree n p
  have hint (w : ERNeighbor n v) :
      Integrable (edgeIndicator (incidentEdge v w)) (erdosRenyi n p) := by
    exact (edgeIndicator_isBernoulli p (incidentEdge v w)).integrable_comp id
  rw [integral_finsetSum Finset.univ (fun w _ ↦ hint w)]
  simp_rw [(edgeIndicator_isBernoulli p (incidentEdge v _)).integral_eq]
  simp [expectedDegree, ERNeighbor]

/-- The event that `v` is isolated.

**Lean implementation helper.** -/
def isolated {n : ℕ} (v : Fin n) : Set (ERSample n) :=
  {G | ∀ w : ERNeighbor n v, edgeIndicator (incidentEdge v w) G = 0}

/-- A vertex is isolated exactly when every incident edge indicator vanishes.

**Lean implementation helper.** -/
lemma isolated_eq_iInter {n : ℕ} (v : Fin n) :
    isolated v = ⋂ w : ERNeighbor n v, edgeIndicator (incidentEdge v w) ⁻¹' {0} := by
  ext G
  simp [isolated]

/-- The event that a fixed vertex is isolated is measurable.

**Lean implementation helper.** -/
lemma isolated_measurable {n : ℕ} (v : Fin n) : MeasurableSet (isolated v) := by
  rw [isolated_eq_iInter]
  exact MeasurableSet.iInter fun _ ↦
    (by fun_prop : Measurable (edgeIndicator (incidentEdge v _))) (measurableSet_singleton 0)

/-- Every edge indicator is nonnegative.

**Lean implementation helper.** -/
lemma edgeIndicator_nonneg {n : ℕ} (e : EREdge n) (G : ERSample n) :
    0 ≤ edgeIndicator e G := by
  by_cases h : G e <;> simp [edgeIndicator, h]

/-- Characterizes `isolated` by the equivalent condition `degree_eq_zero`.

**Lean implementation helper.** -/
lemma isolated_iff_degree_eq_zero {n : ℕ} (v : Fin n) (G : ERSample n) :
    G ∈ isolated v ↔ degree v G = 0 := by
  rw [degree, Fintype.sum_eq_zero_iff_of_nonneg fun w ↦
    edgeIndicator_nonneg (incidentEdge v w) G]
  change (∀ w : ERNeighbor n v, edgeIndicator (incidentEdge v w) G = 0) ↔
    (fun w : ERNeighbor n v ↦ edgeIndicator (incidentEdge v w) G) = 0
  constructor
  · intro h
    funext w
    exact h w
  · intro h w
    simpa using congrFun h w

/-- A fixed vertex is isolated with probability `(1-p)^(n-1)`.

**Lean implementation helper.** -/
theorem isolated_probability {n : ℕ} (p : I) (v : Fin n) :
    (erdosRenyi n p).real (isolated v) = (1 - (p : ℝ)) ^ (n - 1) := by
  have h := (incident_independent p v).measure_inter_preimage_eq_mul
    (S := Finset.univ) (sets := fun _ : ERNeighbor n v ↦ ({0} : Set ℝ)) (by simp)
  simp only [Finset.mem_univ, Set.iInter_true] at h
  rw [isolated_eq_iInter, measureReal_def, h, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, edge_absent_probability]
  simp [ERNeighbor]

end HDP
