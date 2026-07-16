import HighDimensionalProbability.Prelude.Matrix
import HighDimensionalProbability.Prelude.RandomVector
import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Shared finite random-matrix infrastructure

This file contains only source-neutral definitions.  A random matrix is kept as
an ordinary function into a finite matrix type; rows, columns, Gram matrices and
sample second-moment matrices are therefore definitionally transparent.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace ENNReal

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A finite real random matrix. -/
abbrev RandomMatrix (m n : Type*) (Ω : Type*) := Ω → Matrix m n ℝ

/-- The `i`th row of a random matrix as a Euclidean random vector.

**Lean implementation helper.** -/
def randomMatrixRow {m n : Type*} [Fintype n]
    (A : RandomMatrix m n Ω) (i : m) : Ω → EuclideanSpace ℝ n :=
  fun ω => WithLp.toLp 2 (A ω i)

/-- The `j`th column of a random matrix as a Euclidean random vector.

**Lean implementation helper.** -/
def randomMatrixColumn {m n : Type*} [Fintype m]
    (A : RandomMatrix m n Ω) (j : n) : Ω → EuclideanSpace ℝ m :=
  fun ω => WithLp.toLp 2 (fun i => A ω i j)

/-- The centered version of a scalar random-matrix entry.

**Lean implementation helper.** -/
noncomputable def centeredEntry {m n : Type*}
    (A : RandomMatrix m n Ω) (i : m) (j : n) (μ : Measure Ω) : Ω → ℝ :=
  fun ω => A ω i j - ∫ ξ, A ξ i j ∂μ

/-- Entrywise measurability of a finite random matrix.

**Lean implementation helper.** -/
def RandomMatrix.AEMeasurableEntries {m n : Type*}
    (A : RandomMatrix m n Ω) (μ : Measure Ω) : Prop :=
  ∀ i j, AEMeasurable (fun ω => A ω i j) μ

/-- Rowwise measurability of a finite random matrix.

**Lean implementation helper.** -/
def RandomMatrix.AEMeasurableRows {m n : Type*} [Fintype n]
    (A : RandomMatrix m n Ω) (μ : Measure Ω) : Prop :=
  ∀ i, AEMeasurable (randomMatrixRow A i) μ

/-- Genuine entrywise measurability of a finite random matrix. This is the
appropriate interface for finite-process concentration results whose public
API asks for `Measurable`, rather than merely `AEMeasurable`, sample paths.

**Lean implementation helper.** -/
def RandomMatrix.MeasurableEntries {m n : Type*} [MeasurableSpace Ω]
    (A : RandomMatrix m n Ω) : Prop :=
  ∀ i j, Measurable (fun ω => A ω i j)

/-- Genuine rowwise measurability of a finite random matrix.

**Lean implementation helper.** -/
def RandomMatrix.MeasurableRows {m n : Type*} [MeasurableSpace Ω] [Fintype n]
    (A : RandomMatrix m n Ω) : Prop :=
  ∀ i, Measurable (randomMatrixRow A i)

/-- Entrywise centering. This is also the coordinatewise meaning of a
centered finite-dimensional row.

**Lean implementation helper.** -/
def RandomMatrix.CenteredEntries {m n : Type*}
    (A : RandomMatrix m n Ω) (μ : Measure Ω) : Prop :=
  ∀ i j, ∫ ω, A ω i j ∂μ = 0

/-- Rowwise centering, encoded coordinatewise. In finite dimension this is
equivalent to zero Bochner mean whenever the rows are integrable, while this
definition remains safe before integrability has been established.

**Lean implementation helper.** -/
def RandomMatrix.CenteredRows {m n : Type*} [Fintype n]
    (A : RandomMatrix m n Ω) (μ : Measure Ω) : Prop :=
  ∀ i j, ∫ ω, randomMatrixRow A i ω j ∂μ = 0

/-- Every scalar entry is subgaussian.

**Lean implementation helper.** -/
def RandomMatrix.SubGaussianEntries {m n : Type*}
    (A : RandomMatrix m n Ω) (μ : Measure Ω) : Prop :=
  ∀ i j, SubGaussian (fun ω => A ω i j) μ

/-- Every row is a subgaussian random vector.

**Lean implementation helper.** -/
def RandomMatrix.SubGaussianRows {m : Type*} {n : ℕ}
    (A : RandomMatrix m (Fin n) Ω) (μ : Measure Ω) : Prop :=
  ∀ i, SubGaussianVector (randomMatrixRow A i) μ

/-- A uniform scalar-entry ψ₂ bound.

**Lean implementation helper.** -/
def RandomMatrix.EntryPsi2Bound {m n : Type*}
    (A : RandomMatrix m n Ω) (μ : Measure Ω) (K : ℝ) : Prop :=
  ∀ i j, psi2Norm (fun ω => A ω i j) μ ≤ K

/-- A uniform row-vector ψ₂ bound.

**Lean implementation helper.** -/
def RandomMatrix.RowPsi2Bound {m : Type*} {n : ℕ}
    (A : RandomMatrix m (Fin n) Ω) (μ : Measure Ω) (K : ℝ) : Prop :=
  ∀ i, psi2NormVector (randomMatrixRow A i) μ ≤ K

/-- Finiteness certificate for the real-valued row ψ₂ suprema. Keeping
this separate from `RowPsi2Bound` makes every use of `csSup` explicit.

**Lean implementation helper.** -/
def RandomMatrix.RowPsi2Finite {m : Type*} {n : ℕ}
    (A : RandomMatrix m (Fin n) Ω) (μ : Measure Ω) : Prop :=
  ∀ i, BddAbove {r : ℝ | ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
    r = psi2Norm (fun ω => inner ℝ (randomMatrixRow A i ω) u) μ}

/-- Every row has identity second moment.

**Lean implementation helper.** -/
def RandomMatrix.IsotropicRows {m : Type*} {n : ℕ}
    (A : RandomMatrix m (Fin n) Ω) (μ : Measure Ω) : Prop :=
  ∀ i, IsIsotropic (randomMatrixRow A i) μ

/-- The `j`th coordinate of random row `i` is the matrix entry `A(ω)_{ij}`.

**Lean implementation helper.** -/
@[simp]
theorem randomMatrixRow_apply {m n : Type*} [Fintype n]
    (A : RandomMatrix m n Ω) (i : m) (ω : Ω) (j : n) :
    randomMatrixRow A i ω j = A ω i j := rfl

/-- Entrywise measurability gives genuine row-vector measurability.

**Lean implementation helper.** -/
theorem RandomMatrix.AEMeasurableEntries.aemeasurable_row
    {m n : Type*} [Fintype n] {A : RandomMatrix m n Ω}
    (hA : A.AEMeasurableEntries μ) (i : m) :
    AEMeasurable (randomMatrixRow A i) μ := by
  have hpi : AEMeasurable (fun ω => fun j => A ω i j) μ :=
    aemeasurable_pi_lambda _ (hA i)
  exact (MeasurableEquiv.toLp 2 (n → ℝ)).measurable.comp_aemeasurable hpi

/-- Almost-everywhere measurability of all matrix entries implies almost-everywhere measurability of every random row.

**Lean implementation helper.** -/
theorem RandomMatrix.AEMeasurableEntries.aemeasurable_rows
    {m n : Type*} [Fintype n] {A : RandomMatrix m n Ω}
    (hA : A.AEMeasurableEntries μ) : A.AEMeasurableRows μ :=
  fun i => hA.aemeasurable_row i

/-- Row-vector measurability recovers every scalar entry.

**Lean implementation helper.** -/
theorem RandomMatrix.AEMeasurableRows.aemeasurable_entry
    {m n : Type*} [Fintype n] {A : RandomMatrix m n Ω}
    (hA : A.AEMeasurableRows μ) (i : m) (j : n) :
    AEMeasurable (fun ω => A ω i j) μ := by
  have hpi : AEMeasurable (fun ω => (randomMatrixRow A i ω).ofLp) μ :=
    (MeasurableEquiv.toLp 2 (n → ℝ)).symm.measurable.comp_aemeasurable (hA i)
  simpa using hpi.eval j

/-- Characterizes `RandomMatrix.aemeasurableEntries` by the equivalent condition `rows`.

**Lean implementation helper.** -/
theorem RandomMatrix.aemeasurableEntries_iff_rows
    {m n : Type*} [Fintype n] {A : RandomMatrix m n Ω} :
    A.AEMeasurableEntries μ ↔ A.AEMeasurableRows μ := by
  constructor
  · exact RandomMatrix.AEMeasurableEntries.aemeasurable_rows
  · intro h i j
    exact h.aemeasurable_entry i j

/-- Entrywise measurability gives genuine row-vector measurability.

**Lean implementation helper.** -/
theorem RandomMatrix.MeasurableEntries.measurable_row
    {m n : Type*} [MeasurableSpace Ω] [Fintype n]
    {A : RandomMatrix m n Ω}
    (hA : A.MeasurableEntries) (i : m) :
    Measurable (randomMatrixRow A i) := by
  have hpi : Measurable (fun ω => fun j => A ω i j) :=
    measurable_pi_lambda _ (hA i)
  exact (MeasurableEquiv.toLp 2 (n → ℝ)).measurable.comp hpi

/-- Measurability of all matrix entries implies measurability of every random row.

**Lean implementation helper.** -/
theorem RandomMatrix.MeasurableEntries.measurable_rows
    {m n : Type*} [MeasurableSpace Ω] [Fintype n]
    {A : RandomMatrix m n Ω}
    (hA : A.MeasurableEntries) : A.MeasurableRows :=
  fun i => hA.measurable_row i

/-- Genuine row-vector measurability recovers every scalar entry.

**Lean implementation helper.** -/
theorem RandomMatrix.MeasurableRows.measurable_entry
    {m n : Type*} [MeasurableSpace Ω] [Fintype n]
    {A : RandomMatrix m n Ω}
    (hA : A.MeasurableRows) (i : m) (j : n) :
    Measurable (fun ω => A ω i j) := by
  change Measurable (fun ω => randomMatrixRow A i ω j)
  exact (PiLp.continuous_apply (p := (2 : ℝ≥0∞))
    (fun _ : n => ℝ) j).measurable.comp (hA i)

/-- In finite dimension, genuine entrywise and rowwise measurability are
equivalent.

**Lean implementation helper.** -/
theorem RandomMatrix.measurableEntries_iff_rows
    {m n : Type*} [MeasurableSpace Ω] [Fintype n]
    {A : RandomMatrix m n Ω} :
    A.MeasurableEntries ↔ A.MeasurableRows := by
  constructor
  · exact RandomMatrix.MeasurableEntries.measurable_rows
  · intro h i j
    exact h.measurable_entry i j

/-- Genuine entrywise measurability supplies the existing almost-everywhere
entry interface for every measure.

**Lean implementation helper.** -/
theorem RandomMatrix.MeasurableEntries.aemeasurable_entries
    {m n : Type*} [MeasurableSpace Ω] {A : RandomMatrix m n Ω}
    (hA : A.MeasurableEntries) (μ : Measure Ω) :
    A.AEMeasurableEntries μ :=
  fun i j => (hA i j).aemeasurable

/-- Genuine rowwise measurability supplies the existing almost-everywhere row
interface for every measure.

**Lean implementation helper.** -/
theorem RandomMatrix.MeasurableRows.aemeasurable_rows
    {m n : Type*} [MeasurableSpace Ω] [Fintype n]
    {A : RandomMatrix m n Ω}
    (hA : A.MeasurableRows) (μ : Measure Ω) :
    A.AEMeasurableRows μ :=
  fun i => (hA i).aemeasurable

/-- Coordinatewise row centering is exactly entrywise centering.

**Lean implementation helper.** -/
theorem RandomMatrix.centeredRows_iff_entries
    {m n : Type*} [Fintype n] {A : RandomMatrix m n Ω} :
    A.CenteredRows μ ↔ A.CenteredEntries μ := by
  rfl

/-- Expansion of a scalar row marginal in matrix coordinates.

**Lean implementation helper.** -/
theorem inner_randomMatrixRow {m n : Type*} [Fintype n]
    (A : RandomMatrix m n Ω) (i : m) (ω : Ω)
    (u : EuclideanSpace ℝ n) :
    inner ℝ (randomMatrixRow A i ω) u = ∑ j, A ω i j * u j := by
  simp [randomMatrixRow, PiLp.inner_apply, mul_comm]

/-- Centered, integrable entries give centered one-dimensional row
marginals.

**Lean implementation helper.** -/
theorem RandomMatrix.CenteredRows.integral_inner_eq_zero
    {m n : Type*} [Fintype n] {A : RandomMatrix m n Ω}
    (hcenter : A.CenteredRows μ)
    (hint : ∀ i j, Integrable (fun ω => A ω i j) μ)
    (i : m) (u : EuclideanSpace ℝ n) :
    ∫ ω, inner ℝ (randomMatrixRow A i ω) u ∂μ = 0 := by
  simp_rw [inner_randomMatrixRow]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j _
    rw [integral_mul_const, (centeredRows_iff_entries.mp hcenter) i j, zero_mul]
  · intro j _
    exact (hint i j).mul_const (u j)

/-- Row subgaussianity specializes to every scalar row marginal.

**Lean implementation helper.** -/
theorem RandomMatrix.SubGaussianRows.marginal
    {m : Type*} {n : ℕ} {A : RandomMatrix m (Fin n) Ω}
    (hA : A.SubGaussianRows μ) (i : m)
    (u : EuclideanSpace ℝ (Fin n)) :
    SubGaussian (fun ω => inner ℝ (randomMatrixRow A i ω) u) μ :=
  hA i u

/-- Row measurability specializes to every scalar row marginal.

**Lean implementation helper.** -/
theorem RandomMatrix.AEMeasurableRows.aemeasurable_marginal
    {m : Type*} {n : ℕ} {A : RandomMatrix m (Fin n) Ω}
    (hA : A.AEMeasurableRows μ) (i : m)
    (u : EuclideanSpace ℝ (Fin n)) :
    AEMeasurable (fun ω => inner ℝ (randomMatrixRow A i ω) u) μ :=
  (hA i).inner_const

/-- Genuine row measurability specializes to every scalar row marginal.

**Lean implementation helper.** -/
theorem RandomMatrix.MeasurableRows.measurable_marginal
    {m : Type*} {n : ℕ} [MeasurableSpace Ω]
    {A : RandomMatrix m (Fin n) Ω}
    (hA : A.MeasurableRows) (i : m)
    (u : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun ω => inner ℝ (randomMatrixRow A i ω) u) :=
  (hA i).inner_const

/-- Independence of all scalar entries, indexed by the product type.

**Lean implementation helper.** -/
def RandomMatrix.IndependentEntries {m n : Type*}
    (A : RandomMatrix m n Ω) (μ : Measure Ω) : Prop :=
  iIndepFun (fun ij : m × n => fun ω => A ω ij.1 ij.2) μ

/-- Independence of the row random vectors.

**Lean implementation helper.** -/
def RandomMatrix.IndependentRows {m n : Type*} [Fintype n]
    (A : RandomMatrix m n Ω) (μ : Measure Ω) : Prop :=
  iIndepFun (fun i => randomMatrixRow A i) μ

/-- The normalized sample Gram matrix `m⁻¹ Aᵀ A`. The explicit natural
sample size avoids silently dividing by a type cardinality.

**Lean implementation helper.** -/
noncomputable def normalizedGram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (sampleSize : ℕ)
    (A : Matrix m n ℝ) : Matrix n n ℝ :=
  (sampleSize : ℝ)⁻¹ • HDP.gramMatrix A

/-- The sample (uncentered) second-moment matrix of finitely many vectors.

**Lean implementation helper.** -/
noncomputable def sampleSecondMoment {m n : Type*} [Fintype m] [Fintype n]
    (sampleSize : ℕ) (X : m → EuclideanSpace ℝ n) : Matrix n n ℝ :=
  Matrix.of fun j k => (sampleSize : ℝ)⁻¹ * ∑ i, X i j * X i k

/-- The `(j,k)` sample second-moment entry is the normalized sum of coordinate products `X_{ij}X_{ik}`.

**Lean implementation helper.** -/
@[simp]
theorem sampleSecondMoment_apply {m n : Type*} [Fintype m] [Fintype n]
    (sampleSize : ℕ) (X : m → EuclideanSpace ℝ n) (j k : n) :
    sampleSecondMoment sampleSize X j k =
      (sampleSize : ℝ)⁻¹ * ∑ i, X i j * X i k := rfl

/-- Rows recover the normalized Gram matrix entrywise.

**Lean implementation helper.** -/
theorem normalizedGram_eq_sampleSecondMoment_rows
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (sampleSize : ℕ)
    (A : Matrix m n ℝ) :
    normalizedGram sampleSize A =
      sampleSecondMoment sampleSize
        (fun i => WithLp.toLp 2 (A i)) := by
  ext j k
  simp [normalizedGram, gramMatrix, Matrix.mul_apply,
    sampleSecondMoment]

/-- Fintype-indexed form of the Chapter 2 subgaussian sum theorem. Chapter
4 naturally indexes matrix entries by a product type rather than `Fin N`.

**Lean implementation helper.** -/
theorem psi2Norm_fintype_sum_sq_le [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, SubGaussian (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hindep : iIndepFun X μ) :
    SubGaussian (fun ω => ∑ i, X i ω) μ ∧
      psi2Norm (fun ω => ∑ i, X i ω) μ ^ 2 ≤
        30 * ∑ i, psi2Norm (X i) μ ^ 2 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Y : Fin (Fintype.card ι) → Ω → ℝ := fun k => X (e.symm k)
  have h := psi2Norm_sum_sq_le (X := Y)
    (fun k => hXm (e.symm k)) (fun k => hX (e.symm k))
    (fun k => hmean (e.symm k)) (hindep.precomp e.symm.injective)
  have hfun : (fun ω => ∑ k, Y k ω) = (fun ω => ∑ i, X i ω) := by
    funext ω
    exact e.symm.sum_comp (fun i => X i ω)
  have hsum : (∑ k, psi2Norm (Y k) μ ^ 2) =
      ∑ i, psi2Norm (X i) μ ^ 2 := by
    exact e.symm.sum_comp (fun i => psi2Norm (X i) μ ^ 2)
  rw [hfun, hsum] at h
  exact h

end HDP
