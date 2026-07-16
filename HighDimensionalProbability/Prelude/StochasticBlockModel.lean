import HighDimensionalProbability.Prelude.Basic
import HighDimensionalProbability.Prelude.RandomMatrix
import Mathlib.Data.Sym.Card
import Mathlib.MeasureTheory.Integral.Pi

/-!
# A finite loop-aware two-community stochastic block model

Unlike `SimpleGraph`, the source model in Book Definition 4.5.1 includes
self-loops.  We therefore use one independent Bernoulli coordinate for every
unordered pair in `Sym2 (Fin (2*k))`, including diagonal pairs.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal unitInterval

namespace HDP

/-- Vertices in the balanced two-community model. -/
abbrev SBMVertex (k : ℕ) := Fin (2 * k)

/-- Unordered pairs, including self-loops. -/
abbrev SBMEdge (k : ℕ) := Sym2 (SBMVertex k)

/-- A loop-aware graph sample. -/
abbrev SBMSample (k : ℕ) := SBMEdge k → Bool

/-- Community membership: the first `k` vertices are `false`, the rest `true`.

**Lean implementation helper.** -/
def sbmCommunity {k : ℕ} (i : SBMVertex k) : Bool := decide (k ≤ i.1)

/-- Whether two vertices belong to the same community.

**Lean implementation helper.** -/
def sbmSameCommunity {k : ℕ} (i j : SBMVertex k) : Bool :=
  sbmCommunity i == sbmCommunity j

/-- The relation saying that two stochastic-block-model vertices share a community is symmetric.

**Lean implementation helper.** -/
@[simp]
lemma sbmSameCommunity_comm {k : ℕ} (i j : SBMVertex k) :
    sbmSameCommunity i j = sbmSameCommunity j i := by
  simp [sbmSameCommunity, eq_comm]

/-- The Bernoulli parameter attached to an unordered pair.

**Lean implementation helper.** -/
def sbmEdgeProbability {k : ℕ} (p q : I) : SBMEdge k → I :=
  Sym2.lift ⟨fun i j => if sbmSameCommunity i j then p else q, by
    intro i j
    change (if (sbmCommunity i == sbmCommunity j) = true then p else q) =
      (if (sbmCommunity j == sbmCommunity i) = true then p else q)
    rw [Bool.beq_comm]⟩

/-- An edge receives probability `p` within a community and probability `q` across communities.

**Lean implementation helper.** -/
@[simp]
lemma sbmEdgeProbability_mk {k : ℕ} (p q : I) (i j : SBMVertex k) :
    sbmEdgeProbability p q s(i, j) =
      if sbmSameCommunity i j then p else q := rfl

/-- The finite product probability measure `G(2k,p,q)`, with loops.

**Lean implementation helper.** -/
noncomputable def stochasticBlockModel (k : ℕ) (p q : I) :
    Measure (SBMSample k) :=
  Measure.pi fun e : SBMEdge k => bernoulliMeasure true false (sbmEdgeProbability p q e)

noncomputable instance stochasticBlockModel.isProbabilityMeasure
    {k : ℕ} {p q : I} : IsProbabilityMeasure (stochasticBlockModel k p q) := by
  rw [stochasticBlockModel]
  infer_instance

/-- Real indicator of an unordered SBM coordinate.

**Lean implementation helper.** -/
def sbmEdgeIndicator {k : ℕ} (e : SBMEdge k) (G : SBMSample k) : ℝ :=
  if G e then 1 else 0

/-- The loop-aware symmetric adjacency matrix.

**Lean implementation helper.** -/
def sbmAdjacencyMatrix {k : ℕ} (G : SBMSample k) :
    Matrix (SBMVertex k) (SBMVertex k) ℝ :=
  fun i j => sbmEdgeIndicator s(i, j) G

/-- The adjacency entry at vertices `i,j` is the indicator of their unordered edge coordinate.

**Lean implementation helper.** -/
@[simp]
lemma sbmAdjacencyMatrix_apply {k : ℕ} (G : SBMSample k)
    (i j : SBMVertex k) :
    sbmAdjacencyMatrix G i j = sbmEdgeIndicator s(i, j) G := rfl

/-- The adjacency matrix of an undirected stochastic-block-model sample is symmetric.

**Lean implementation helper.** -/
lemma sbmAdjacencyMatrix_symmetric {k : ℕ} (G : SBMSample k) :
    (sbmAdjacencyMatrix G).transpose = sbmAdjacencyMatrix G := by
  ext i j
  simp [sbmAdjacencyMatrix, Sym2.eq_swap]

/-- Every unordered coordinate has its prescribed Bernoulli law.

**Lean implementation helper.** -/
lemma sbmEdgeIndicator_isBernoulli {k : ℕ} (p q : I) (e : SBMEdge k) :
    IsBernoulli (sbmEdgeIndicator e) (sbmEdgeProbability p q e)
      (stochasticBlockModel k p q) := by
  refine ⟨by fun_prop, ?_⟩
  change Measure.map ((fun b : Bool => if b then (1 : ℝ) else 0) ∘ fun G => G e)
      (Measure.pi fun f : SBMEdge k =>
        bernoulliMeasure true false (sbmEdgeProbability p q f)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), Measure.pi_map_eval]
  convert map_bernoulliMeasure true false
    (fun b : Bool => if b then (1 : ℝ) else 0) (sbmEdgeProbability p q e) using 1 <;>
    simp

/-- All unordered coordinates (including loop coordinates) are independent.

**Lean implementation helper.** -/
lemma sbmEdgeIndicator_independent {k : ℕ} (p q : I) :
    iIndepFun (fun e : SBMEdge k => sbmEdgeIndicator e)
      (stochasticBlockModel k p q) := by
  change iIndepFun
    (fun e : SBMEdge k => fun G => if G e then (1 : ℝ) else 0)
    (Measure.pi fun e : SBMEdge k =>
      bernoulliMeasure true false (sbmEdgeProbability p q e))
  exact iIndepFun_pi
    (X := fun _ : SBMEdge k => fun b : Bool => if b then (1 : ℝ) else 0)
    (μ := fun e : SBMEdge k =>
      bernoulliMeasure true false (sbmEdgeProbability p q e))
    (fun _ => by fun_prop)

/-- The deterministic expected adjacency matrix.

**Lean implementation helper.** -/
noncomputable def sbmExpectedAdjacency (k : ℕ) (p q : I) :
    Matrix (SBMVertex k) (SBMVertex k) ℝ :=
  fun i j => if sbmSameCommunity i j then (p : ℝ) else (q : ℝ)

/-- Entrywise expectation of the loop-aware adjacency matrix.

**Lean implementation helper.** -/
theorem integral_sbmAdjacencyMatrix_apply {k : ℕ} (p q : I)
    (i j : SBMVertex k) :
    ∫ G, sbmAdjacencyMatrix G i j ∂(stochasticBlockModel k p q) =
      sbmExpectedAdjacency k p q i j := by
  change (∫ G, sbmEdgeIndicator s(i, j) G
      ∂(stochasticBlockModel k p q)) = _
  rw [(sbmEdgeIndicator_isBernoulli p q s(i, j)).integral_eq]
  rw [sbmEdgeProbability_mk]
  unfold sbmExpectedAdjacency
  split <;> rfl

/-- Community labels as real signs.

**Lean implementation helper.** -/
def sbmCommunityLabel {k : ℕ} (i : SBMVertex k) : ℝ :=
  if sbmCommunity i then -1 else 1

/-- Spectral sign classifier with the source's tie convention: zero belongs
to the negative community.

**Lean implementation helper.** -/
noncomputable def spectralSignLabel {ι : Type*} (v : ι → ℝ) (i : ι) : ℝ :=
  if 0 < v i then 1 else -1

/-- Misclassified vertices, minimized over the unavoidable global sign.

**Lean implementation helper.** -/
noncomputable def misclassifiedUpToSign {ι : Type*} [Fintype ι]
    (truth estimate : ι → ℝ) : ℕ :=
  min ((Finset.univ.filter fun i => spectralSignLabel estimate i ≠ truth i).card)
    ((Finset.univ.filter fun i => spectralSignLabel (fun j => -estimate j) i ≠ truth i).card)

/-- A coordinate whose sign disagrees with a `±1` truth label contributes at
least one unit of squared Euclidean error.

**Lean implementation helper.** -/
lemma one_le_sq_sub_of_sign_mismatch {a x : ℝ}
    (ha : a = 1 ∨ a = -1) (hmis : spectralSignLabel (fun _ : Unit => x) () ≠ a) :
    1 ≤ (a - x) ^ 2 := by
  rcases ha with rfl | rfl
  · unfold spectralSignLabel at hmis
    split_ifs at hmis
    · exact (hmis rfl).elim
    · nlinarith
  · unfold spectralSignLabel at hmis
    split_ifs at hmis
    · nlinarith
    · exact (hmis rfl).elim

end HDP
