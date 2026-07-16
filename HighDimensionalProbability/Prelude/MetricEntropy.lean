/-
Shared metric-entropy infrastructure for Book Chapter 4.

Mathlib's `Metric.coveringNumber`, `Metric.externalCoveringNumber`, and
`Metric.packingNumber` take values in `ℕ∞`.  Those extended-natural values are the
authoritative interface here.  The natural-valued wrapper below is deliberately
available only together with a finiteness proof.
-/
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice

open Set
open scoped ENNReal NNReal

namespace HDP

/-! ## Covers and finite witnesses -/

variable {X : Type*} [PseudoEMetricSpace X]

/-- Book terminology: an `ε`-net is Mathlib's internal metric cover. -/
abbrev IsEpsilonNet (ε : ℝ≥0) (K N : Set X) : Prop :=
  N ⊆ K ∧ Metric.IsCover ε K N

/-- A finite internal `ε`-net, retaining its subset and cover certificates. -/
structure FiniteNet (ε : ℝ≥0) (K : Set X) where
  points : Set X
  subset : points ⊆ K
  finite : points.Finite
  isCover : Metric.IsCover ε K points

/-- The canonical finite-set realization of a `FiniteNet`. This is
noncomputable only because a general metric space does not carry a chosen
decidable equality.

**Lean implementation helper.** -/
noncomputable def FiniteNet.toFinset {ε : ℝ≥0} {K : Set X}
    (N : FiniteNet ε K) : Finset X :=
  N.finite.toFinset

/-- Every point of a finite net belongs to its underlying finset.

**Lean implementation helper.** -/
@[simp]
theorem FiniteNet.mem_toFinset {ε : ℝ≥0} {K : Set X}
    (N : FiniteNet ε K) (x : X) :
    x ∈ N.toFinset ↔ x ∈ N.points := by
  simp [FiniteNet.toFinset]

/-- Coercing the underlying finset of a finite net to a set recovers the net's point set.

**Lean implementation helper.** -/
@[simp, norm_cast]
theorem FiniteNet.coe_toFinset {ε : ℝ≥0} {K : Set X}
    (N : FiniteNet ε K) :
    (N.toFinset : Set X) = N.points := by
  ext x
  simp

/-- The internal-net certificate transported to the canonical `Finset`.

**Lean implementation helper.** -/
theorem FiniteNet.toFinset_subset {ε : ℝ≥0} {K : Set X}
    (N : FiniteNet ε K) :
    (N.toFinset : Set X) ⊆ K := by
  simpa using N.subset

/-- The cover certificate transported to the canonical `Finset`.

**Lean implementation helper.** -/
theorem FiniteNet.isCover_toFinset {ε : ℝ≥0} {K : Set X}
    (N : FiniteNet ε K) :
    Metric.IsCover ε K (N.toFinset : Set X) := by
  simpa using N.isCover

/-- The cardinality of a finite net is the cardinality of its underlying finset.

**Lean implementation helper.** -/
@[simp]
theorem FiniteNet.card_toFinset {ε : ℝ≥0} {K : Set X}
    (N : FiniteNet ε K) :
    N.toFinset.card = N.points.ncard := by
  simpa [FiniteNet.toFinset] using
    (Set.ncard_eq_toFinset_card N.points N.finite).symm

/-- Safe cardinal cast for finite-net counting arguments. The target is
Mathlib's authoritative extended-natural cardinality, so no `⊤ ↦ 0`
conversion is involved.

**Lean implementation helper.** -/
@[simp, norm_cast]
theorem FiniteNet.coe_card_toFinset {ε : ℝ≥0} {K : Set X}
    (N : FiniteNet ε K) :
    (N.toFinset.card : ℕ∞) = N.points.encard := by
  simpa [FiniteNet.toFinset] using
    N.finite.encard_eq_coe_toFinset_card.symm

/-- Package a concrete finite internal cover as a `FiniteNet`.

**Lean implementation helper.** -/
def FiniteNet.ofFinset {ε : ℝ≥0} {K : Set X} (N : Finset X)
    (hsubset : (N : Set X) ⊆ K)
    (hcover : Metric.IsCover ε K (N : Set X)) : FiniteNet ε K where
  points := N
  subset := hsubset
  finite := N.finite_toSet
  isCover := hcover

/-- Converting a finite net built from a finset back to a finset recovers the original finset.

**Lean implementation helper.** -/
@[simp]
theorem FiniteNet.toFinset_ofFinset {ε : ℝ≥0} {K : Set X} (N : Finset X)
    (hsubset : (N : Set X) ⊆ K)
    (hcover : Metric.IsCover ε K (N : Set X)) :
    (FiniteNet.ofFinset N hsubset hcover).toFinset = N := by
  ext x
  simp [FiniteNet.ofFinset]

/-- The natural value of a finite covering number. The proof argument prevents
silently turning the value `⊤` into zero through `ENat.toNat`.

**Lean implementation helper.** -/
noncomputable def finiteCoveringNumber (ε : ℝ≥0) (K : Set X)
    (_hfinite : Metric.coveringNumber ε K ≠ ⊤) : ℕ :=
  (Metric.coveringNumber ε K).toNat

/-- The analogous safe natural-valued packing number.

**Lean implementation helper.** -/
noncomputable def finitePackingNumber (ε : ℝ≥0) (K : Set X)
    (_hfinite : Metric.packingNumber ε K ≠ ⊤) : ℕ :=
  (Metric.packingNumber ε K).toNat

/-- When the covering number is finite, coercing its natural-number representative recovers the original cardinal.

**Lean implementation helper.** -/
@[simp]
theorem coe_finiteCoveringNumber (ε : ℝ≥0) (K : Set X)
    (hfinite : Metric.coveringNumber ε K ≠ ⊤) :
    (finiteCoveringNumber ε K hfinite : ℕ∞) = Metric.coveringNumber ε K := by
  exact ENat.coe_toNat hfinite

/-- When the packing number is finite, coercing its natural-number representative recovers the original cardinal.

**Lean implementation helper.** -/
@[simp]
theorem coe_finitePackingNumber (ε : ℝ≥0) (K : Set X)
    (hfinite : Metric.packingNumber ε K ≠ ⊤) :
    (finitePackingNumber ε K hfinite : ℕ∞) = Metric.packingNumber ε K := by
  exact ENat.coe_toNat hfinite

/-- A finite set has finite internal covering and packing numbers.

**Lean implementation helper.** -/
theorem finite_covering_packing_of_finite {K : Set X} (hK : K.Finite) (ε : ℝ≥0) :
    Metric.coveringNumber ε K ≠ ⊤ ∧ Metric.packingNumber ε K ≠ ⊤ := by
  constructor
  · exact ne_top_of_le_ne_top hK.encard_lt_top.ne
      (Metric.coveringNumber_le_encard_self K)
  · exact ne_top_of_le_ne_top hK.encard_lt_top.ne
      (Metric.packingNumber_le_encard_self K)

/-- A finite minimal cover, packaged for use by finite-union arguments.

**Lean implementation helper.** -/
noncomputable def minimalFiniteNet (ε : ℝ≥0) (K : Set X)
    (hfinite : Metric.coveringNumber ε K ≠ ⊤) : FiniteNet ε K where
  points := Metric.minimalCover ε K
  subset := Metric.minimalCover_subset
  finite := Metric.finite_minimalCover
  isCover := Metric.isCover_minimalCover hfinite

/-- A Minkowski sum, named as in the source Definition 4.2.9.

**Book Definition 4.2.9.** -/
def minkowskiSum {E : Type*} [Add E] (A B : Set E) : Set E :=
  {x | ∃ a ∈ A, ∃ b ∈ B, a + b = x}

/-- Characterizes membership in `minkowskiSum`.

**Lean implementation helper.** -/
@[simp]
theorem mem_minkowskiSum {E : Type*} [Add E] {A B : Set E} {x : E} :
    x ∈ minkowskiSum A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = x := by
  rfl

/-! ## The binary Hamming cube -/

/-- Binary words of length `n`, equipped with Mathlib's Hamming metric. -/
abbrev BinaryWord (n : ℕ) := Hamming (fun _ : Fin n => Bool)

/-- The integer-valued Hamming distance underlying the metric on `BinaryWord n`.

**Lean implementation helper.** -/
def hammingDistance {n : ℕ} (x y : BinaryWord n) : ℕ :=
  hammingDist (Hamming.ofHamming x) (Hamming.ofHamming y)

/-- The metric distance between binary words is their integer-valued Hamming distance, coerced to `ℝ`.

**Lean implementation helper.** -/
@[simp]
theorem dist_binaryWord_eq_hammingDistance {n : ℕ} (x y : BinaryWord n) :
    dist x y = hammingDistance x y := rfl

/-- The nonnegative distance between binary words is their Hamming distance, coerced to `ℝ≥0`.

**Lean implementation helper.** -/
@[simp]
theorem nndist_binaryWord_eq_hammingDistance {n : ℕ} (x y : BinaryWord n) :
    nndist x y = hammingDistance x y := rfl

/-- Hamming distance on binary words is symmetric.

**Lean implementation helper.** -/
theorem hammingDistance_comm {n : ℕ} (x y : BinaryWord n) :
    hammingDistance x y = hammingDistance y x :=
  hammingDist_comm _ _

/-- Hamming distance on binary words satisfies the triangle inequality.

**Lean implementation helper.** -/
theorem hammingDistance_triangle {n : ℕ} (x y z : BinaryWord n) :
    hammingDistance x z ≤ hammingDistance x y + hammingDistance y z :=
  @hammingDist_triangle (Fin n) (fun _ => Bool) _ _
    (Hamming.ofHamming x) (Hamming.ofHamming y) (Hamming.ofHamming z)

/-- Bounds `hammingDistance` above by `length`.

**Lean implementation helper.** -/
theorem hammingDistance_le_length {n : ℕ} (x y : BinaryWord n) :
    hammingDistance x y ≤ n := by
  simpa [hammingDistance] using
    (@hammingDist_le_card_fintype (Fin n) (fun _ => Bool) _ _
      (Hamming.ofHamming x) (Hamming.ofHamming y))

end HDP
