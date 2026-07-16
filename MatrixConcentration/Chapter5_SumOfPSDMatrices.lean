import MatrixConcentration.Chapter3_MatrixLaplaceTransformMethod
import MatrixConcentration.Chapter4_MatrixGaussianAndRademacherSeries
import MatrixConcentration.Appendix_MatrixRosenthal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.List.GetD
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Chapter 5: Sums of positive-semidefinite random matrices

This consolidated chapter contains:

* **Book §§5.1 and 5.4:** matrix Chernoff mgf, cgf, tail, and expectation bounds;
* **Book §5.1:** simplified Chernoff inequalities and optimality comparisons;
* **Book §5.2:** random column, row, and column submatrix applications;
* **Book §5.3:** compression and graph-Laplacian prerequisites;
* **Book §5.3.3:** Erdős–Rényi graph connectivity estimates.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Matrix Chernoff: mgf and cgf bounds (Tropp §5.4, Lemma 5.4.1)

* `chernoff_matrix_mgf_le`/`chernoff_matrix_cgf_le` — **Book Lemma 5.4.1**
  (C5-20): for a random Hermitian matrix `X` with
  `0 ≤ λ_min(X)` and `λ_max(X) ≤ L`, and every `θ ∈ ℝ`,
  `𝔼 e^{θX} ≼ exp(g(θ)·𝔼X)` and `log 𝔼 e^{θX} ≼ g(θ)·𝔼X`, where
  `g(θ) = (e^{θL} − 1)/L`.  Faithful translation of the source proof: the
  convexity chord bound `e^{θx} ≤ 1 + g(θ)x` on `[0, L]`, the Transfer Rule
  (2.1.14), monotonicity of expectation for the semidefinite order (§2.2.5),
  the bound `I + A ≼ e^A` (Transfer Rule at `1 + a ≤ e^a`), and the operator
  monotonicity of the logarithm (2.1.18).
* Bernoulli moment lemmas (C5-10): `ae_range_isBernoulli`,
  `integral_isBernoulli` (`𝔼 f(δ) = p f(1) + (1−p) f(0)`),
  `integral_id_isBernoulli` (`𝔼δ = p`), `integrable_isBernoulli` — the facts
  the chapter's examples use about BERNOULLI(p) modulators (§5.2, §5.3),
  mirroring the Chapter-4 Rademacher lemmas.
* Eigenvalue-interval bridges (implicit prerequisites of the standing
  hypotheses `0 ≤ λ_min(X_k)`, `λ_max(X_k) ≤ L`):
  `posSemidef_of_lambdaMin_nonneg`, `l2_opNorm_le_of_eigenvalue_bounds`
  (`‖X‖ ≤ L`, feeding the Chapter-3 master bounds), and
  `eq_zero_of_eigenvalue_bounds` (the degenerate case `L = 0`).

-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℂ}

section Bernoulli

variable [IsProbabilityMeasure μ]

/-- Lean implementation helper (C5-10): a BERNOULLI(p) variable takes the values
`0` and `1` almost surely. -/
lemma ae_range_isBernoulli {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {δ : Ω → ℝ}
    (hδm : Measurable δ) (hδ : IsBernoulli p δ μ) :
    ∀ᵐ ω ∂μ, δ ω = 0 ∨ δ ω = 1 := by
  have hS : MeasurableSet ({0, 1} : Set ℝ) :=
    (measurableSet_singleton 0).union (measurableSet_singleton 1)
  have h1 : μ.map δ {0, 1} = 1 := by
    rw [show μ.map δ = bernoulliMeasureReal p from hδ, bernoulliMeasureReal]
    rw [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply' _ hS,
      MeasureTheory.Measure.dirac_apply' _ hS]
    rw [Set.indicator_of_mem (by simp : (1:ℝ) ∈ ({0,1} : Set ℝ)),
      Set.indicator_of_mem (by simp : (0:ℝ) ∈ ({0,1} : Set ℝ))]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp.1 (by linarith [hp.2])]
    norm_num
  have h2 : μ (δ ⁻¹' {0, 1}) = 1 := by
    rw [← MeasureTheory.Measure.map_apply hδm hS]
    exact h1
  have h3 : μ (δ ⁻¹' {0, 1})ᶜ = 0 := by
    rw [MeasureTheory.measure_compl (hδm hS) (by simp), h2]
    simp
  refine MeasureTheory.ae_iff.mpr ?_
  have h4 : {ω | ¬(δ ω = 0 ∨ δ ω = 1)} = (δ ⁻¹' {0, 1})ᶜ := by
    ext ω
    simp [Set.mem_preimage]
  rw [h4]
  exact h3

/-- Lean implementation helper (C5-10): all moments of a Bernoulli variable exist. -/
lemma integrable_isBernoulli {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {δ : Ω → ℝ}
    (hδm : Measurable δ) (hδ : IsBernoulli p δ μ) {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable (fun ω => f (δ ω)) μ := by
  refine Integrable.of_bound (hf.comp hδm).aestronglyMeasurable
    (max |f 0| |f 1|) ?_
  filter_upwards [ae_range_isBernoulli hp hδm hδ] with ω h
  rcases h with h | h <;> rw [h, Real.norm_eq_abs]
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- Lean implementation helper: the expectation of a function of a Bernoulli
variable, `𝔼 f(δ) = p·f(1) + (1−p)·f(0)`. This is the recovered prerequisite
used throughout **Book §5.2–§5.3** through `𝔼δ_k = p` and `δ_k² = δ_k`. -/
lemma integral_isBernoulli {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {δ : Ω → ℝ}
    (hδm : Measurable δ) (hδ : IsBernoulli p δ μ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ ω, f (δ ω) ∂μ = p * f 1 + (1 - p) * f 0 := by
  have h1 : ∫ ω, f (δ ω) ∂μ = ∫ x, f x ∂(μ.map δ) :=
    (MeasureTheory.integral_map hδm.aemeasurable hf.aestronglyMeasurable).symm
  rw [h1, show μ.map δ = bernoulliMeasureReal p from hδ, bernoulliMeasureReal]
  rw [MeasureTheory.integral_add_measure
      ((MeasureTheory.integrable_dirac (by simp [enorm_lt_top])).smul_measure
        (by simp))
      ((MeasureTheory.integrable_dirac (by simp [enorm_lt_top])).smul_measure
        (by simp)),
    MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_dirac, MeasureTheory.integral_dirac]
  rw [ENNReal.toReal_ofReal hp.1, ENNReal.toReal_ofReal (by linarith [hp.2])]
  simp [smul_eq_mul]

/-- **Book §5.2** (C5-10): `𝔼δ = p` for a Bernoulli variable. Implicit source
declaration. -/
lemma integral_id_isBernoulli {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {δ : Ω → ℝ}
    (hδm : Measurable δ) (hδ : IsBernoulli p δ μ) :
    ∫ ω, δ ω ∂μ = p := by
  have h := integral_isBernoulli (f := fun x => x) hp hδm hδ measurable_id
  rw [h]
  ring

end Bernoulli

section EigenvalueBridges

/-- **Book §5.4**, implicit prerequisite: the standing eigenvalue hypotheses give the
uniform norm bound `‖X‖ ≤ L` consumed by the Chapter-3 master bounds. -/
lemma l2_opNorm_le_of_eigenvalue_bounds [Nonempty n] {L : ℝ} (hA : A.IsHermitian)
    (hmin : 0 ≤ lambdaMin hA) (hmax : lambdaMax hA ≤ L) : ‖A‖ ≤ L := by
  have hpsd : A.PosSemidef := posSemidef_of_lambdaMin_nonneg hA hmin
  rw [posSemidef_l2_opNorm_eq_lambdaMax hpsd]
  exact hmax

/-- Lean implementation helper: the degenerate case `L = 0` of the Chernoff
hypotheses forces the matrix to vanish (all eigenvalues are trapped at zero). -/
lemma eq_zero_of_eigenvalue_bounds [Nonempty n] (hA : A.IsHermitian)
    (hmin : 0 ≤ lambdaMin hA) (hmax : lambdaMax hA ≤ 0) : A = 0 := by
  have hnorm : ‖A‖ ≤ 0 := l2_opNorm_le_of_eigenvalue_bounds hA hmin hmax
  exact norm_le_zero_iff.mp hnorm

end EigenvalueBridges

section ChordAndExp

/-- **Book §5.4**, proof of **Lemma 5.4.1**: the convexity chord bound
`e^{θx} ≤ 1 + ((e^{θL} − 1)/L)·x` for `x ∈ [0, L]` — "Since `f` is convex, its
graph lies below the chord connecting any two points on the graph."  Implicit
source declaration (displayed inside the proof). -/
lemma exp_le_one_add_chord {L : ℝ} (hL : 0 < L) (θ : ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) L) :
    Real.exp (θ * x) ≤ 1 + (Real.exp (θ * L) - 1) / L * x := by
  obtain ⟨hx0, hxL⟩ := hx
  have ha : (0 : ℝ) ≤ 1 - x / L := by
    rw [sub_nonneg, div_le_one hL]
    exact hxL
  have hb : (0 : ℝ) ≤ x / L := div_nonneg hx0 hL.le
  have hab : (1 - x / L) + x / L = 1 := by ring
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (θ * L))
    ha hb hab
  have hLne : L ≠ 0 := ne_of_gt hL
  have harg : (1 - x / L) • (0 : ℝ) + (x / L) • (θ * L) = θ * x := by
    rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
    rw [show x / L * (θ * L) = θ * x * (L / L) from by ring, div_self hLne,
      mul_one]
  rw [harg] at h
  calc Real.exp (θ * x) ≤ (1 - x / L) • Real.exp 0 + (x / L) • Real.exp (θ * L) := h
  _ = 1 + (Real.exp (θ * L) - 1) / L * x := by
      rw [Real.exp_zero, smul_eq_mul, smul_eq_mul, mul_one]
      field_simp
      ring

/-- Lean implementation helper: the cfc of an affine function is the affine
combination `a•I + s•A`. -/
lemma cfc_affine (hA : A.IsHermitian) (a s : ℝ) :
    cfc (fun x : ℝ => a + s * x) A = a • (1 : Matrix n n ℂ) + s • A := by
  have h1 : cfc (fun x : ℝ => a + s * x) A =
      cfc (fun _ : ℝ => a) A + cfc (fun x : ℝ => s * x) A := cfc_add A _ _
  rw [h1, cfc_const a A, smul_eq_cfc hA s]
  congr 1
  rw [Algebra.algebraMap_eq_smul_one]

/-- **Book §5.4**, proof of **Lemma 5.4.1**: `I + A ≼ e^A` for every Hermitian matrix,
"which we obtain by applying the Transfer Rule to the inequality `1 + a ≤ e^a`".
Implicit source declaration. -/
lemma one_add_le_exp_matrix (hA : A.IsHermitian) :
    (1 : Matrix n n ℂ) + A ≤ NormedSpace.exp A := by
  have h1 : (1 : Matrix n n ℂ) + A = cfc (fun x : ℝ => 1 + 1 * x) A := by
    rw [cfc_affine hA 1 1, one_smul, one_smul]
  have h2 : NormedSpace.exp A = cfc Real.exp A := matrixExp_eq_cfc hA
  rw [h1, h2]
  refine transfer_rule hA (I := Set.univ) (fun i => Set.mem_univ _)
    fun x _ => ?_
  rw [one_mul, add_comm]
  exact Real.add_one_le_exp x

end ChordAndExp

section MgfCgfBound

variable [IsProbabilityMeasure μ]

/-- **Book Lemma 5.4.1**: the coefficient `g(θ) = (e^{θL} − 1)/L` of the Chernoff
mgf/cgf bound.  Implicit source declaration (the displayed function `g` of
(5.4.1)/(5.4.2)). -/
noncomputable def gChernoff (θ L : ℝ) : ℝ := (Real.exp (θ * L) - 1) / L

variable {X : Ω → Matrix n n ℂ} {L : ℝ}

/-- Lean implementation helper: entrywise integrability of a bounded random
matrix, from the eigenvalue bounds. -/
lemma mintegrable_of_eigenvalue_bounds [Nonempty n]
    (hXm : Measurable X) (hherm : ∀ ω, (X ω).IsHermitian)
    (hmin : ∀ ω, 0 ≤ lambdaMin (hherm ω)) (hmax : ∀ ω, lambdaMax (hherm ω) ≤ L) :
    MIntegrable X μ := by
  refine MIntegrable.of_bound hXm L (Filter.Eventually.of_forall fun ω i j => ?_)
  calc ‖X ω i j‖ ≤ ‖X ω‖ := norm_entry_le_l2_opNorm _ _ _
  _ ≤ L := l2_opNorm_le_of_eigenvalue_bounds (hherm ω) (hmin ω) (hmax ω)

/-- Lean implementation helper: the expectation of an affine image,
`𝔼(I + s•X) = I + s•𝔼X`. -/
lemma expectation_one_add_smul (hX : MIntegrable X μ) (s : ℝ) :
    expectation μ (fun ω => (1 : Matrix n n ℂ) + s • X ω) =
      1 + s • expectation μ X := by
  ext i j
  rw [expectation_apply]
  have h1 : (fun ω => ((1 : Matrix n n ℂ) + s • X ω) i j) =
      fun ω => (1 : Matrix n n ℂ) i j + s • X ω i j := by
    funext ω
    rw [Matrix.add_apply, Matrix.smul_apply]
  have h2 : Integrable (fun ω => s • X ω i j) μ := (hX i j).smul s
  rw [h1, MeasureTheory.integral_add (integrable_const _) h2,
    MeasureTheory.integral_const, MeasureTheory.integral_smul]
  rw [MeasureTheory.probReal_univ, one_smul, Matrix.add_apply, Matrix.smul_apply,
    expectation_apply]

/-- **Book Lemma 5.4.1 (Matrix Chernoff: Mgf Bound)**
(§5.4), first half: if `0 ≤ λ_min(X)` and `λ_max(X) ≤ L`, then
`𝔼 e^{θX} ≼ exp(((e^{θL}−1)/L)·𝔼X)` for all `θ ∈ ℝ`.  Explicit source
declaration; faithful translation of the source proof (chord bound + Transfer
Rule + expectation monotonicity + `I + A ≼ e^A`). -/
theorem chernoff_matrix_mgf_le [Nonempty n]
    (hXm : Measurable X) (hherm : ∀ ω, (X ω).IsHermitian)
    (hmin : ∀ ω, 0 ≤ lambdaMin (hherm ω)) (hmax : ∀ ω, lambdaMax (hherm ω) ≤ L)
    (hL : 0 ≤ L) (θ : ℝ) :
    matrixMgf μ X θ ≤ NormedSpace.exp (gChernoff θ L • expectation μ X) := by
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · -- degenerate case `L = 0`: the matrix vanishes identically
    have hX0 : ∀ ω, X ω = 0 := fun ω =>
      eq_zero_of_eigenvalue_bounds (hherm ω) (hmin ω) (hL0 ▸ hmax ω)
    have h1 : matrixMgf μ X θ = 1 := by
      rw [matrixMgf, show (fun ω => NormedSpace.exp (θ • X ω)) =
        fun _ => (1 : Matrix n n ℂ) from funext fun ω => by
          rw [hX0 ω, smul_zero, NormedSpace.exp_zero],
        expectation_const (μ := μ) 1]
    have h2 : expectation μ X = 0 := by
      rw [show X = fun _ => (0 : Matrix n n ℂ) from funext hX0,
        expectation_const (μ := μ) 0]
    rw [h1, h2, smul_zero, NormedSpace.exp_zero]
  · -- main case `L > 0`
    set g : ℝ := gChernoff θ L with hgdef
    -- pointwise transfer: `e^{θX(ω)} ≼ I + g·X(ω)`
    have hpt : ∀ ω, NormedSpace.exp (θ • X ω) ≤ 1 + g • X ω := by
      intro ω
      have h1 : NormedSpace.exp (θ • X ω) =
          cfc (fun x : ℝ => Real.exp (θ * x)) (X ω) :=
        exp_smul_eq_cfc (hherm ω) θ
      have h2 : (1 : Matrix n n ℂ) + g • X ω =
          cfc (fun x : ℝ => 1 + g * x) (X ω) := by
        rw [cfc_affine (hherm ω) 1 g, one_smul]
      rw [h1, h2]
      refine transfer_rule (hherm ω) (I := Set.Icc 0 L) (fun i => ?_)
        fun x hx => ?_
      · exact ⟨(hmin ω).trans (lambdaMin_le_eigenvalues (hherm ω) i),
          (eigenvalues_le_lambdaMax (hherm ω) i).trans (hmax ω)⟩
      · exact exp_le_one_add_chord hLpos θ hx
    -- integrate the pointwise bound
    have hXint : MIntegrable X μ :=
      mintegrable_of_eigenvalue_bounds hXm hherm hmin hmax
    have hexpint : MIntegrable (fun ω => NormedSpace.exp (θ • X ω)) μ := by
      have h := mintegrable_matrixExp_of_bound (μ := μ)
        (hXm.const_smul θ) (fun ω => isHermitian_real_smul (hherm ω) θ)
        (R := |θ| * L) (fun ω => by
          show ‖θ • X ω‖ ≤ |θ| * L
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left
            (l2_opNorm_le_of_eigenvalue_bounds (hherm ω) (hmin ω) (hmax ω))
            (abs_nonneg θ))
      exact h
    have haffint : MIntegrable (fun ω => (1 : Matrix n n ℂ) + g • X ω) μ := by
      intro i j
      have h1 : (fun ω => ((1 : Matrix n n ℂ) + g • X ω) i j) =
          fun ω => (1 : Matrix n n ℂ) i j + g • X ω i j := by
        funext ω
        rw [Matrix.add_apply, Matrix.smul_apply]
      rw [h1]
      exact (integrable_const _).add ((hXint i j).smul g)
    have hmono := expectation_loewner_mono hexpint haffint
      (Filter.Eventually.of_forall hpt)
    rw [expectation_one_add_smul hXint g] at hmono
    -- `I + g·𝔼X ≼ exp(g·𝔼X)`
    have hEherm : (expectation μ X).IsHermitian :=
      isHermitian_expectation (Filter.Eventually.of_forall hherm)
    have hfinal := one_add_le_exp_matrix (isHermitian_real_smul hEherm g)
    exact le_trans hmono hfinal

/-- **Book Lemma 5.4.1 (Matrix Chernoff: Cgf Bound)**
(§5.4), second half: under the same hypotheses,
`log 𝔼 e^{θX} ≼ ((e^{θL}−1)/L)·𝔼X` for all `θ ∈ ℝ` — "we simply take the
logarithm of the semidefinite bound for the mgf … because the logarithm is
operator monotone" (2.1.18).  Explicit source declaration. -/
theorem chernoff_matrix_cgf_le [Nonempty n]
    (hXm : Measurable X) (hherm : ∀ ω, (X ω).IsHermitian)
    (hmin : ∀ ω, 0 ≤ lambdaMin (hherm ω)) (hmax : ∀ ω, lambdaMax (hherm ω) ≤ L)
    (hL : 0 ≤ L) (θ : ℝ) :
    matrixCgf μ X θ ≤ gChernoff θ L • expectation μ X := by
  have hmgf := chernoff_matrix_mgf_le (μ := μ) hXm hherm hmin hmax hL θ
  have hpd : (matrixMgf μ X θ).PosDef :=
    posDef_matrixMgf hXm hherm
      (fun ω => l2_opNorm_le_of_eigenvalue_bounds (hherm ω) (hmin ω) (hmax ω)) θ
  have hEherm : (expectation μ X).IsHermitian :=
    isHermitian_expectation (Filter.Eventually.of_forall hherm)
  have hgherm : (gChernoff θ L • expectation μ X).IsHermitian :=
    isHermitian_real_smul hEherm _
  have hpd2 : (NormedSpace.exp (gChernoff θ L • expectation μ X)).PosDef :=
    posDef_exp hgherm
  have hlog := log_monotone hpd hpd2 hmgf
  rwa [show CFC.log (NormedSpace.exp (gChernoff θ L • expectation μ X)) =
    gChernoff θ L • expectation μ X from
    CFC.log_exp _ hgherm.isSelfAdjoint] at hlog

end MgfCgfBound

end MatrixConcentration



set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The Matrix Chernoff Inequalities (Tropp §5.1, Theorem 5.1.1)

* `matrix_chernoff_expectation_lower` — **Book (5.1.3)**;
* `matrix_chernoff_expectation_upper` — **Book (5.1.4)**;
* `matrix_chernoff_tail_lower` — **Book (5.1.5)**;
* `matrix_chernoff_tail_upper` — **Book (5.1.6)**;
* `expectation_matsum_eq` and `chernoff_mu_min_eq`/`chernoff_mu_max_eq` — the
  identities **Book (5.1.1)/(5.1.2)** defining `μ_min`/`μ_max` (both displayed forms agree);
* `chernoff_cgf_trace_bound_upper/_lower` — the §5.4 substitution chains

  `tr exp(Σ_k Ξ_k(θ)) ≤ d·exp(g(θ)·μ_max)` (resp. `μ_min` for `θ < 0`).

The proofs follow §5.4 exactly: the cgf bound (Lemma 5.4.1) is substituted into
the four master inequalities (3.6.1)–(3.6.4) using the trace-exp monotonicity
(2.1.16), the bound `tr M ≤ d·λ_max(M)`, the Spectral Mapping Theorem
(`λ_max(e^A) = e^{λ_max(A)}`), the positive homogeneity (2.1.4) (resp. the sign
rule (2.1.5) for `θ < 0`), and the changes of variables `θ ↦ θ/L`
(resp. `θ ↦ −θ/L`); the tails take `θ = L⁻¹ log(1±ε)`.

Hypothesis conventions: the standing assumptions `0 ≤ λ_min(X_k)`,
`λ_max(X_k) ≤ L` are taken verbatim; `0 ≤ L` is implicit in the source (it
follows from the hypotheses whenever the family and the dimension are
nonempty).  The degenerate cases `L = 0` (all summands vanish) and `ε = 0`
(both tail bounds reduce to `P ≤ 1 ≤ d`) are handled explicitly; the source
implicitly assumes nondegeneracy.

-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ]
variable {X : ι → Ω → Matrix n n ℂ} {L : ℝ}

section MuStatistics

end MuStatistics

section TraceBounds

variable [Nonempty n]

/-- **Book §5.4** (proof of Theorem 5.1.1, maximum-eigenvalue chain, C5-21):
for `θ > 0` and `L > 0`,
`tr exp(Σ_k Ξ_{X_k}(θ)) ≤ d·exp(g(θ)·μ_max)` with `g(θ) = (e^{θL}−1)/L`.
Implicit source declaration (the displayed chain). -/
lemma chernoff_cgf_trace_bound_upper
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L)
    (hL : 0 < L) {θ : ℝ} (hθ : 0 < θ) :
    ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re ≤
      (Fintype.card n : ℝ) *
        Real.exp (gChernoff θ L * lambdaMax (isHermitian_sum_expectation (μ := μ) hherm)) := by
  have hg : 0 ≤ gChernoff θ L := by
    rw [gChernoff]
    have h1 : (1 : ℝ) ≤ Real.exp (θ * L) := Real.one_le_exp (by positivity)
    have h2 : (0 : ℝ) ≤ Real.exp (θ * L) - 1 := by linarith
    positivity
  -- substitute the cgf bounds and use trace-exp monotonicity
  have hcgf_le : ∀ k, matrixCgf μ (X k) θ ≤ gChernoff θ L • expectation μ (X k) :=
    fun k => chernoff_matrix_cgf_le (μ := μ) (hmeas k) (hherm k) (hmin k)
      (hmax k) hL.le θ
  have hsum_le : (∑ k, matrixCgf μ (X k) θ) ≤
      gChernoff θ L • ∑ k, expectation μ (X k) := by
    rw [Finset.smul_sum]
    exact sum_loewner_mono Finset.univ fun k _ => hcgf_le k
  have hcgfHerm : (∑ k, matrixCgf μ (X k) θ).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => isHermitian_cfc_log _
  have hEsumHerm : (∑ k, expectation μ (X k)).IsHermitian :=
    isHermitian_sum_expectation (μ := μ) hherm
  have hgEHerm : (gChernoff θ L • ∑ k, expectation μ (X k)).IsHermitian :=
    isHermitian_real_smul hEsumHerm _
  have h1 := trace_exp_monotone hcgfHerm hgEHerm hsum_le
  refine h1.trans ?_
  -- `tr exp(g·Σ𝔼X) ≤ d·λ_max(exp(·)) = d·e^{g·μ_max}`
  have h2 := trace_re_le_card_mul_lambdaMax (isHermitian_exp hgEHerm)
  refine h2.trans ?_
  rw [lambdaMax_exp hgEHerm, lambdaMax_smul_nonneg hEsumHerm hg hgEHerm]

/-- **Book §5.4** (minimum-eigenvalue chain, C5-21): for `θ < 0` and `L > 0`,
`tr exp(Σ_k Ξ_{X_k}(θ)) ≤ d·exp(g(θ)·μ_min)` — "we move to the fourth line by
invoking the property `λ_max(αA) = α λ_min(A)` for `α < 0` … this piece of
algebra depends on the fact that `g(θ) < 0` when `θ < 0`."  Implicit source
declaration. -/
lemma chernoff_cgf_trace_bound_lower
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L)
    (hL : 0 < L) {θ : ℝ} (hθ : θ < 0) :
    ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re ≤
      (Fintype.card n : ℝ) *
        Real.exp (gChernoff θ L * lambdaMin (isHermitian_sum_expectation (μ := μ) hherm)) := by
  have hg : gChernoff θ L ≤ 0 := by
    rw [gChernoff]
    have h1 : Real.exp (θ * L) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg hθ.le hL.le)
    have h2 : Real.exp (θ * L) - 1 ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg h2 hL.le
  have hcgf_le : ∀ k, matrixCgf μ (X k) θ ≤ gChernoff θ L • expectation μ (X k) :=
    fun k => chernoff_matrix_cgf_le (μ := μ) (hmeas k) (hherm k) (hmin k)
      (hmax k) hL.le θ
  have hsum_le : (∑ k, matrixCgf μ (X k) θ) ≤
      gChernoff θ L • ∑ k, expectation μ (X k) := by
    rw [Finset.smul_sum]
    exact sum_loewner_mono Finset.univ fun k _ => hcgf_le k
  have hcgfHerm : (∑ k, matrixCgf μ (X k) θ).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => isHermitian_cfc_log _
  have hEsumHerm : (∑ k, expectation μ (X k)).IsHermitian :=
    isHermitian_sum_expectation (μ := μ) hherm
  have hgEHerm : (gChernoff θ L • ∑ k, expectation μ (X k)).IsHermitian :=
    isHermitian_real_smul hEsumHerm _
  have h1 := trace_exp_monotone hcgfHerm hgEHerm hsum_le
  refine h1.trans ?_
  have h2 := trace_re_le_card_mul_lambdaMax (isHermitian_exp hgEHerm)
  refine h2.trans ?_
  rw [lambdaMax_exp hgEHerm, lambdaMax_smul_nonpos hEsumHerm hg hgEHerm]

end TraceBounds

section MainTheorem

variable [Nonempty n]

/-- Lean implementation helper: the degenerate case `L = 0` — every summand
vanishes identically, so the sum, its eigenvalues, and the μ-statistics vanish. -/
lemma chernoff_degenerate_zero
    (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ 0) :
    ∀ k ω, X k ω = 0 := fun k ω =>
  eq_zero_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)

/-- Lean implementation helper: `λ_max(0) = 0` and `λ_min(0) = 0`. -/
lemma lambdaMax_zero_matrix (h : (0 : Matrix n n ℂ).IsHermitian) :
    lambdaMax h = 0 := by
  have h1 := abs_lambdaMax_le h
  rw [norm_zero] at h1
  exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))

/-- Lean implementation helper: `λ_min(0) = 0`. -/
lemma lambdaMin_zero_matrix (h : (0 : Matrix n n ℂ).IsHermitian) :
    lambdaMin h = 0 := by
  have h1 : ∀ i, h.eigenvalues i = 0 := fun i => by
    have h2 := abs_eigenvalues_le_l2_opNorm h i
    rw [norm_zero] at h2
    exact abs_eq_zero.mp (le_antisymm h2 (abs_nonneg _))
  show (⨅ i, h.eigenvalues i) = 0
  rw [show h.eigenvalues = fun _ => (0 : ℝ) from funext h1]
  exact ciInf_const

/-- Lean implementation helper: transport of `λ_min` along an equality. -/
lemma lambdaMin_congr {A B : Matrix n n ℂ} (h : A = B) (hA : A.IsHermitian)
    (hB : B.IsHermitian) : lambdaMin hA = lambdaMin hB := by
  subst h
  rfl

/-- **Book Theorem 5.1.1 (Matrix Chernoff), equation (5.1.4)**:
`𝔼 λ_max(Y) ≤ ((e^θ − 1)/θ)·μ_max + θ⁻¹·L·log d` for every `θ > 0`.
Explicit source declaration; §5.4 proof (master bound (3.6.1) + cgf
substitution + change of variables `θ ↦ θ/L`). -/
theorem matrix_chernoff_expectation_upper
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) {θ : ℝ} (hθ : 0 < θ) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ ≤
      (Real.exp θ - 1) / θ * lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) +
        θ⁻¹ * L * Real.log (Fintype.card n) := by
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · -- degenerate case: everything vanishes
    have hX0 := chernoff_degenerate_zero hherm hmin (fun k ω => hL0 ▸ hmax k ω)
    have hY0 : ∀ ω, (∑ k, X k ω) = 0 := fun ω =>
      Finset.sum_eq_zero fun k _ => hX0 k ω
    have hE0 : (∑ k, expectation μ (X k)) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [show X k = fun _ => (0 : Matrix n n ℂ) from funext fun ω => hX0 k ω,
        expectation_const (μ := μ) 0]
    have hlhs : (∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ∂μ) = 0 := by
      have hfun : (fun ω => lambdaMax (isHermitian_matsum Finset.univ
          (fun k => hherm k ω))) = fun _ => (0 : ℝ) := by
        funext ω
        rw [lambdaMax_congr (hY0 ω) (isHermitian_matsum Finset.univ
          (fun k => hherm k ω)) Matrix.isHermitian_zero]
        exact lambdaMax_zero_matrix _
      rw [hfun]
      simp
    rw [hlhs]
    have hmu : lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) = 0 := by
      rw [lambdaMax_congr hE0 (isHermitian_sum_expectation (μ := μ) hherm)
        Matrix.isHermitian_zero]
      exact lambdaMax_zero_matrix _
    rw [hmu, ← hL0]
    simp
  · -- main case `L > 0`: master bound at `θ' = θ/L`
    have hθ' : 0 < θ / L := div_pos hθ hLpos
    have hR : ∀ k ω, ‖X k ω‖ ≤ (fun _ : ι => L) k := fun k ω =>
      l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
    have h1 := master_expectation_upper (μ := μ) hmeas hherm hR hind hθ'
    refine h1.trans ?_
    have h2 := chernoff_cgf_trace_bound_upper (μ := μ) hmeas hherm hmin hmax
      hLpos hθ'
    have hpos : 0 < ((NormedSpace.exp (∑ k, matrixCgf μ (X k) (θ / L))).trace).re :=
      trace_exp_re_pos (isHermitian_matsum Finset.univ fun k =>
        isHermitian_cfc_log _)
    have h3 : Real.log ((NormedSpace.exp
        (∑ k, matrixCgf μ (X k) (θ / L))).trace).re ≤
        Real.log ((Fintype.card n : ℝ) * Real.exp (gChernoff (θ / L) L *
          lambdaMax (isHermitian_sum_expectation (μ := μ) hherm))) :=
      Real.log_le_log hpos h2
    have h4 : Real.log ((Fintype.card n : ℝ) * Real.exp (gChernoff (θ / L) L *
        lambdaMax (isHermitian_sum_expectation (μ := μ) hherm))) =
        Real.log (Fintype.card n) + gChernoff (θ / L) L *
          lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) := by
      rw [Real.log_mul (by exact_mod_cast Fintype.card_pos.ne')
        (Real.exp_pos _).ne', Real.log_exp]
    have hgval : gChernoff (θ / L) L = (Real.exp θ - 1) / L := by
      rw [gChernoff, div_mul_cancel₀ θ (ne_of_gt hLpos)]
    calc (θ / L)⁻¹ * Real.log ((NormedSpace.exp
        (∑ k, matrixCgf μ (X k) (θ / L))).trace).re
        ≤ (θ / L)⁻¹ * (Real.log (Fintype.card n) + gChernoff (θ / L) L *
          lambdaMax (isHermitian_sum_expectation (μ := μ) hherm)) := by
          rw [← h4]
          exact mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hθ').le
    _ = (Real.exp θ - 1) / θ * lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) +
        θ⁻¹ * L * Real.log (Fintype.card n) := by
        rw [hgval]
        field_simp
        ring

/-- **Book Theorem 5.1.1, equation (5.1.3)**:
`𝔼 λ_min(Y) ≥ ((1 − e^{−θ})/θ)·μ_min − θ⁻¹·L·log d` for every `θ > 0`.
Explicit source declaration; §5.4 proof (master bound (3.6.2) + change of
variables `θ ↦ −θ/L`). -/
theorem matrix_chernoff_expectation_lower
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) {θ : ℝ} (hθ : 0 < θ) :
    (1 - Real.exp (-θ)) / θ * lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) -
        θ⁻¹ * L * Real.log (Fintype.card n) ≤
      ∫ ω, lambdaMin (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ := by
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · have hX0 := chernoff_degenerate_zero hherm hmin (fun k ω => hL0 ▸ hmax k ω)
    have hY0 : ∀ ω, (∑ k, X k ω) = 0 := fun ω =>
      Finset.sum_eq_zero fun k _ => hX0 k ω
    have hE0 : (∑ k, expectation μ (X k)) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [show X k = fun _ => (0 : Matrix n n ℂ) from funext fun ω => hX0 k ω,
        expectation_const (μ := μ) 0]
    have hlhs : (∫ ω, lambdaMin (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ∂μ) = 0 := by
      have hfun : (fun ω => lambdaMin (isHermitian_matsum Finset.univ
          (fun k => hherm k ω))) = fun _ => (0 : ℝ) := by
        funext ω
        rw [lambdaMin_congr (hY0 ω) (isHermitian_matsum Finset.univ
          (fun k => hherm k ω)) Matrix.isHermitian_zero]
        exact lambdaMin_zero_matrix _
      rw [hfun]
      simp
    rw [hlhs]
    have hmu : lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) = 0 := by
      rw [lambdaMin_congr hE0 (isHermitian_sum_expectation (μ := μ) hherm)
        Matrix.isHermitian_zero]
      exact lambdaMin_zero_matrix _
    rw [hmu, ← hL0]
    simp
  · have hθ' : -θ / L < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hθ) hLpos
    have hR : ∀ k ω, ‖X k ω‖ ≤ (fun _ : ι => L) k := fun k ω =>
      l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
    have h1 := master_expectation_lower (μ := μ) hmeas hherm hR hind hθ'
    refine le_trans ?_ h1
    have h2 := chernoff_cgf_trace_bound_lower (μ := μ) hmeas hherm hmin hmax
      hLpos hθ'
    have hpos : 0 < ((NormedSpace.exp
        (∑ k, matrixCgf μ (X k) (-θ / L))).trace).re :=
      trace_exp_re_pos (isHermitian_matsum Finset.univ fun k =>
        isHermitian_cfc_log _)
    have h3 : Real.log ((NormedSpace.exp
        (∑ k, matrixCgf μ (X k) (-θ / L))).trace).re ≤
        Real.log ((Fintype.card n : ℝ) * Real.exp (gChernoff (-θ / L) L *
          lambdaMin (isHermitian_sum_expectation (μ := μ) hherm))) :=
      Real.log_le_log hpos h2
    have h4 : Real.log ((Fintype.card n : ℝ) * Real.exp (gChernoff (-θ / L) L *
        lambdaMin (isHermitian_sum_expectation (μ := μ) hherm))) =
        Real.log (Fintype.card n) + gChernoff (-θ / L) L *
          lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) := by
      rw [Real.log_mul (by exact_mod_cast Fintype.card_pos.ne')
        (Real.exp_pos _).ne', Real.log_exp]
    have hgval : gChernoff (-θ / L) L = (Real.exp (-θ) - 1) / L := by
      rw [gChernoff, div_mul_cancel₀ (-θ) (ne_of_gt hLpos)]
    have hflip : (-θ / L)⁻¹ * Real.log ((NormedSpace.exp
        (∑ k, matrixCgf μ (X k) (-θ / L))).trace).re ≥
        (-θ / L)⁻¹ * (Real.log (Fintype.card n) + gChernoff (-θ / L) L *
          lambdaMin (isHermitian_sum_expectation (μ := μ) hherm)) := by
      rw [← h4]
      exact mul_le_mul_of_nonpos_left h3 (by
        rw [inv_nonpos]
        exact hθ'.le)
    refine le_trans (le_of_eq ?_) hflip
    rw [hgval]
    field_simp
    ring

/-- **Book Theorem 5.1.1, equation (5.1.6)**:
`P(λ_max(Y) ≥ (1+ε)·μ_max) ≤ d·[e^ε/(1+ε)^{1+ε}]^{μ_max/L}` for `ε ≥ 0`.
Explicit source declaration; §5.4 proof (master bound (3.6.3), optimum
`θ = L⁻¹ log(1+ε)`). -/
theorem matrix_chernoff_tail_upper
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | (1 + ε) * lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) ≤
        lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω))} ≤
      (Fintype.card n : ℝ) *
        (Real.exp ε / (1 + ε) ^ (1 + ε)) ^
          (lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) / L) := by
  classical
  have hcard1 : (1 : ℝ) ≤ (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hPle : ∀ S : Set Ω, μ.real S ≤ 1 := fun S => by
    have h := MeasureTheory.measureReal_mono (μ := μ) (Set.subset_univ S)
    rwa [MeasureTheory.probReal_univ] at h
  set μmax : ℝ := lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) with hmudef
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · -- degenerate `L = 0`: `μmax/L = 0`, bracket^0 = 1, bound is `d ≥ 1`
    rw [← hL0, div_zero, Real.rpow_zero, mul_one]
    exact (hPle _).trans hcard1
  rcases eq_or_lt_of_le hε with hε0 | hεpos
  · -- `ε = 0`: bracket = 1
    rw [← hε0]
    norm_num
    exact (hPle _).trans hcard1
  · -- main case
    set θ : ℝ := Real.log (1 + ε) / L with hθdef
    have h1ε : (0 : ℝ) < 1 + ε := by linarith
    have hlogpos : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
    have hθpos : 0 < θ := div_pos hlogpos hLpos
    have hR : ∀ k ω, ‖X k ω‖ ≤ (fun _ : ι => L) k := fun k ω =>
      l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
    have h1 := master_tail_upper (μ := μ) hmeas hherm hR hind
      ((1 + ε) * μmax) hθpos
    refine h1.trans ?_
    have h2 := chernoff_cgf_trace_bound_upper (μ := μ) hmeas hherm hmin hmax
      hLpos hθpos
    have hgval : gChernoff θ L = ε / L := by
      rw [gChernoff, hθdef, div_mul_cancel₀ _ (ne_of_gt hLpos),
        Real.exp_log h1ε]
      ring_nf
    calc Real.exp (-θ * ((1 + ε) * μmax)) *
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re
        ≤ Real.exp (-θ * ((1 + ε) * μmax)) *
          ((Fintype.card n : ℝ) * Real.exp (gChernoff θ L * μmax)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = (Fintype.card n : ℝ) *
          (Real.exp ε / (1 + ε) ^ (1 + ε)) ^ (μmax / L) := by
        rw [hgval]
        rw [show Real.exp (-θ * ((1 + ε) * μmax)) *
            ((Fintype.card n : ℝ) * Real.exp (ε / L * μmax)) =
            (Fintype.card n : ℝ) * (Real.exp (-θ * ((1 + ε) * μmax)) *
              Real.exp (ε / L * μmax)) from by ring,
          ← Real.exp_add,
          Real.rpow_def_of_pos (div_pos (Real.exp_pos _)
            (Real.rpow_pos_of_pos h1ε _)),
          Real.log_div (Real.exp_pos _).ne'
            (Real.rpow_pos_of_pos h1ε _).ne',
          Real.log_exp, Real.log_rpow h1ε, hθdef]
        congr 1
        field_simp
        ring

/-- **Book Theorem 5.1.1, equation (5.1.5)**:
`P(λ_min(Y) ≤ (1−ε)·μ_min) ≤ d·[e^{−ε}/(1−ε)^{1−ε}]^{μ_min/L}` for `ε ∈ [0,1)`.
Explicit source declaration; §5.4 proof (master bound (3.6.4), optimum
`θ = L⁻¹ log(1−ε)`). -/
theorem matrix_chernoff_tail_lower
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    μ.real {ω | lambdaMin (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ≤
        (1 - ε) * lambdaMin (isHermitian_sum_expectation (μ := μ) hherm)} ≤
      (Fintype.card n : ℝ) *
        (Real.exp (-ε) / (1 - ε) ^ (1 - ε)) ^
          (lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) / L) := by
  classical
  have hcard1 : (1 : ℝ) ≤ (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hPle : ∀ S : Set Ω, μ.real S ≤ 1 := fun S => by
    have h := MeasureTheory.measureReal_mono (μ := μ) (Set.subset_univ S)
    rwa [MeasureTheory.probReal_univ] at h
  set μmin : ℝ := lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) with hmudef
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · rw [← hL0, div_zero, Real.rpow_zero, mul_one]
    exact (hPle _).trans hcard1
  rcases eq_or_lt_of_le hε with hε0 | hεpos
  · rw [← hε0]
    norm_num
    exact (hPle _).trans hcard1
  · set θ : ℝ := Real.log (1 - ε) / L with hθdef
    have h1ε : (0 : ℝ) < 1 - ε := by linarith
    have hlogneg : Real.log (1 - ε) < 0 :=
      Real.log_neg h1ε (by linarith)
    have hθneg : θ < 0 := div_neg_of_neg_of_pos hlogneg hLpos
    have hR : ∀ k ω, ‖X k ω‖ ≤ (fun _ : ι => L) k := fun k ω =>
      l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
    have h1 := master_tail_lower (μ := μ) hmeas hherm hR hind
      ((1 - ε) * μmin) hθneg
    refine h1.trans ?_
    have h2 := chernoff_cgf_trace_bound_lower (μ := μ) hmeas hherm hmin hmax
      hLpos hθneg
    have hgval : gChernoff θ L = -ε / L := by
      rw [gChernoff, hθdef, div_mul_cancel₀ _ (ne_of_gt hLpos),
        Real.exp_log h1ε]
      ring_nf
    calc Real.exp (-θ * ((1 - ε) * μmin)) *
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re
        ≤ Real.exp (-θ * ((1 - ε) * μmin)) *
          ((Fintype.card n : ℝ) * Real.exp (gChernoff θ L * μmin)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = (Fintype.card n : ℝ) *
          (Real.exp (-ε) / (1 - ε) ^ (1 - ε)) ^ (μmin / L) := by
        rw [hgval]
        rw [show Real.exp (-θ * ((1 - ε) * μmin)) *
            ((Fintype.card n : ℝ) * Real.exp (-ε / L * μmin)) =
            (Fintype.card n : ℝ) * (Real.exp (-θ * ((1 - ε) * μmin)) *
              Real.exp (-ε / L * μmin)) from by ring,
          ← Real.exp_add,
          Real.rpow_def_of_pos (div_pos (Real.exp_pos _)
            (Real.rpow_pos_of_pos h1ε _)),
          Real.log_div (Real.exp_pos _).ne'
            (Real.rpow_pos_of_pos h1ε _).ne',
          Real.log_exp, Real.log_rpow h1ε, hθdef]
        congr 1
        field_simp
        ring

/-- **Book (5.1.1)**: the two displayed forms of
`μ_min` agree, `λ_min(𝔼Y) = λ_min(Σ_k 𝔼X_k)`.  Explicit source declaration. -/
lemma chernoff_mu_min_eq (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hint : ∀ k, MIntegrable (X k) μ)
    (hEYherm : (expectation μ (fun ω => ∑ k, X k ω)).IsHermitian) :
    lambdaMin hEYherm = lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) :=
  lambdaMin_congr (expectation_matsum_eq hint) _ _

/-- **Book (5.1.2)**: `λ_max(𝔼Y) = λ_max(Σ_k 𝔼X_k)`.
Explicit source declaration. -/
lemma chernoff_mu_max_eq (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hint : ∀ k, MIntegrable (X k) μ)
    (hEYherm : (expectation μ (fun ω => ∑ k, X k ω)).IsHermitian) :
    lambdaMax hEYherm = lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) :=
  lambdaMax_congr (expectation_matsum_eq hint) _ _

/-- Implicit prerequisite (§5.1): the μ-statistics are nonnegative — the sum of
the expectations of psd random matrices is psd.  Lean implementation helper. -/
lemma posSemidef_sum_expectation
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) :
    (∑ k, expectation μ (X k)).PosSemidef := by
  refine posSemidef_matsum Finset.univ fun k => ?_
  exact posSemidef_expectation
    (mintegrable_of_eigenvalue_bounds (hmeas k) (hherm k) (hmin k) (hmax k))
    (Filter.Eventually.of_forall fun ω =>
      posSemidef_of_lambdaMin_nonneg (hherm k ω) (hmin k ω))

/-- Lean implementation helper: `0 ≤ μ_min` and `0 ≤ μ_max`. -/
lemma chernoff_mu_min_nonneg
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) :
    0 ≤ lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) := by
  have hpsd := posSemidef_sum_expectation (μ := μ) hmeas hherm hmin hmax
  exact le_lambdaMin _ fun i => hpsd.eigenvalues_nonneg i

/-- Lean implementation helper: nonnegativity of the upper Chernoff mean parameter. -/
lemma chernoff_mu_max_nonneg
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) :
    0 ≤ lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) := by
  have h1 := chernoff_mu_min_nonneg (μ := μ) hmeas hherm hmin hmax
  refine h1.trans ?_
  obtain ⟨i⟩ := (inferInstance : Nonempty n)
  exact (lambdaMin_le_eigenvalues _ i).trans (eigenvalues_le_lambdaMax _ i)

end MainTheorem

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Simplified and weakened matrix Chernoff bounds (Tropp §5.1.1)

* `matrix_chernoff_expectation_lower_simple`/`_upper_simple` —
  **Book (5.1.7)/(5.1.8)** (C5-02):
  `𝔼λ_min(Y) ≥ 0.63·μ_min − L·log d` and `𝔼λ_max(Y) ≤ 1.72·μ_max + L·log d`
  — "by selecting `θ = 1` … and evaluating the numerical constants";
* `matrix_chernoff_tail_lower_subgaussian`/`matrix_chernoff_tail_upper_exponential`
  — the two unnumbered weakened tail displays of §5.1.1 (C5-03):
  `P(λ_min(Y) ≤ t·μ_min) ≤ d·e^{−(1−t)²μ_min/2L}` for `t ∈ [0,1)`, and
  `P(λ_max(Y) ≥ t·μ_max) ≤ d·(e/t)^{t·μ_max/L}` for `t ≥ e`.
  Their proof uses the scalar entropy
  inequality `(1−ε)log(1−ε) ≥ −ε + ε²/2` on `[0,1)`
  (`entropy_lower_bound`, proved by monotonicity from `log x ≤ x − 1`) and the
  elementary base comparison `e^{t−1}/t^t ≤ (e/t)^t`.

-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ] [Nonempty n]
variable {X : ι → Ω → Matrix n n ℂ} {L : ℝ}

section NumericalConstants

/-- Lean implementation helper: `0.63 ≤ 1 − e⁻¹`. -/
lemma const_lower_bound : (0.63 : ℝ) ≤ 1 - Real.exp (-1) := by
  have h1 : Real.exp (-1) = (Real.exp 1)⁻¹ := by
    rw [Real.exp_neg]
  have h2 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h3 : Real.exp (-1) < 0.37 := by
    rw [h1]
    rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
    nlinarith
  linarith

/-- Lean implementation helper: `e − 1 ≤ 1.72`. -/
lemma const_upper_bound : Real.exp 1 - 1 ≤ (1.72 : ℝ) := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  linarith

end NumericalConstants

section SimplifiedExpectation

/-- **Book (5.1.7)** (§5.1.1, C5-02):
`𝔼 λ_min(Y) ≥ 0.63·μ_min − L·log d`.  Explicit source declaration ("We obtain
these results by selecting `θ = 1` … and evaluating the numerical constants"). -/
theorem matrix_chernoff_expectation_lower_simple
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) :
    0.63 * lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) -
        L * Real.log (Fintype.card n) ≤
      ∫ ω, lambdaMin (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ := by
  have h := matrix_chernoff_expectation_lower (μ := μ) hmeas hherm hmin hmax hL
    hind one_pos
  refine le_trans ?_ h
  have hmu := chernoff_mu_min_nonneg (μ := μ) hmeas hherm hmin hmax
  have hlog : (0 : ℝ) ≤ Real.log (Fintype.card n) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have h1 : (0.63 : ℝ) ≤ (1 - Real.exp (-1)) / 1 := by
    rw [div_one]
    exact const_lower_bound
  have h2 : 0.63 * lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) ≤
      (1 - Real.exp (-1)) / 1 *
        lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) :=
    mul_le_mul_of_nonneg_right h1 hmu
  have h3 : (1 : ℝ)⁻¹ * L * Real.log (Fintype.card n) =
      L * Real.log (Fintype.card n) := by
    rw [inv_one, one_mul]
  linarith

/-- **Book (5.1.8)** (§5.1.1, C5-02):
`𝔼 λ_max(Y) ≤ 1.72·μ_max + L·log d`. Explicit source declaration. -/
theorem matrix_chernoff_expectation_upper_simple
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ ≤
      1.72 * lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) +
        L * Real.log (Fintype.card n) := by
  have h := matrix_chernoff_expectation_upper (μ := μ) hmeas hherm hmin hmax hL
    hind one_pos
  refine h.trans ?_
  have hmu := chernoff_mu_max_nonneg (μ := μ) hmeas hherm hmin hmax
  have h1 : (Real.exp 1 - 1) / 1 ≤ (1.72 : ℝ) := by
    rw [div_one]
    exact const_upper_bound
  have h2 : (Real.exp 1 - 1) / 1 *
      lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) ≤
      1.72 * lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) :=
    mul_le_mul_of_nonneg_right h1 hmu
  have h3 : (1 : ℝ)⁻¹ * L * Real.log (Fintype.card n) =
      L * Real.log (Fintype.card n) := by
    rw [inv_one, one_mul]
  linarith

end SimplifiedExpectation

section WeakenedTails

/-- Lean implementation helper (the scalar heart of the subgaussian weakening,
C5-03): `(1−ε)·log(1−ε) + ε − ε²/2 ≥ 0` on `[0, 1)`, proved by monotonicity
from `log y ≤ y − 1`. -/
lemma entropy_lower_bound {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    0 ≤ (1 - ε) * Real.log (1 - ε) + ε - ε ^ 2 / 2 := by
  set φ : ℝ → ℝ := fun x => (1 - x) * Real.log (1 - x) + x - x ^ 2 / 2 with hφdef
  have hφ0 : φ 0 = 0 := by
    simp [hφdef]
  have hderiv : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      HasDerivAt φ (-Real.log (1 - x) - x) x := by
    intro x hx
    have hx1 : (0 : ℝ) < 1 - x := by linarith [hx.2]
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have h2 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x :=
      h1.log hx1.ne'
    have h3 : HasDerivAt (fun y : ℝ => (1 - y) * Real.log (1 - y))
        ((-1) * Real.log (1 - x) + (1 - x) * (-1 / (1 - x))) x := h1.mul h2
    have h5 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h6 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      have h7 := h5.div_const 2
      have hxx : 2 * x / 2 = x := by ring
      rwa [hxx] at h7
    have h8 : HasDerivAt (fun y : ℝ => y - y ^ 2 / 2) (1 - x) x :=
      (hasDerivAt_id x).sub h6
    have h9 := h3.add h8
    have heq : (-1) * Real.log (1 - x) + (1 - x) * (-1 / (1 - x)) + (1 - x) =
        -Real.log (1 - x) - x := by
      field_simp
      ring
    rw [heq] at h9
    have hshape : ((fun y : ℝ => (1 - y) * Real.log (1 - y)) +
        fun y : ℝ => y - y ^ 2 / 2) = φ := by
      funext y
      show (1 - y) * Real.log (1 - y) + (y - y ^ 2 / 2) = φ y
      rw [hφdef]
      ring
    rwa [hshape] at h9
  rcases eq_or_lt_of_le hε with hε0 | hεpos
  · rw [← hε0]
    simpa using le_of_eq hφ0.symm
  -- monotonicity of `φ` on `[0, ε]`
  have hsub : Set.Icc (0 : ℝ) ε ⊆ Set.Ico (0 : ℝ) 1 := fun x hx =>
    ⟨hx.1, lt_of_le_of_lt hx.2 hε1⟩
  have hcont : ContinuousOn φ (Set.Icc 0 ε) := by
    have hlin : Continuous fun x : ℝ => 1 - x := by fun_prop
    have h1 : ContinuousOn (fun x : ℝ => Real.log (1 - x)) (Set.Icc 0 ε) :=
      Real.continuousOn_log.comp hlin.continuousOn (fun x hx => by
        have hx1 : (0 : ℝ) < 1 - x := by
          have := hsub hx
          linarith [this.2]
        exact Set.mem_compl_singleton_iff.mpr hx1.ne')
    exact (((continuousOn_const.sub continuousOn_id).mul h1).add
      continuousOn_id).sub ((continuousOn_id.pow 2).div_const 2)
  have hdiff : DifferentiableOn ℝ φ (interior (Set.Icc (0 : ℝ) ε)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact (hderiv x (hsub ⟨hx.1.le, hx.2.le⟩)).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ x ∈ interior (Set.Icc (0 : ℝ) ε), 0 ≤ deriv φ x := by
    intro x hx
    rw [interior_Icc] at hx
    have hIco : x ∈ Set.Ico (0 : ℝ) 1 := hsub ⟨hx.1.le, hx.2.le⟩
    rw [(hderiv x hIco).deriv]
    have hx1 : (0 : ℝ) < 1 - x := by linarith [hIco.2]
    have hlog : Real.log (1 - x) ≤ (1 - x) - 1 :=
      Real.log_le_sub_one_of_pos hx1
    linarith
  have hmono : MonotoneOn φ (Set.Icc 0 ε) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 ε) hcont hdiff hnonneg
  have h := hmono (Set.left_mem_Icc.mpr hε) (Set.right_mem_Icc.mpr hε) hε
  rw [hφ0] at h
  exact h

/-- **Book §5.1.1, first weakened tail display** (C5-03):
`P(λ_min(Y) ≤ t·μ_min) ≤ d·e^{−(1−t)²·μ_min/(2L)}` for `t ∈ [0, 1)` — "The
first bound shows that the lower tail of `λ_min(Y)` decays at a subgaussian
rate." Explicit source declaration. -/
theorem matrix_chernoff_tail_lower_subgaussian
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    μ.real {ω | lambdaMin (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ≤
        t * lambdaMin (isHermitian_sum_expectation (μ := μ) hherm)} ≤
      (Fintype.card n : ℝ) *
        Real.exp (-(1 - t) ^ 2 *
          lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) / (2 * L)) := by
  classical
  set μmin : ℝ := lambdaMin (isHermitian_sum_expectation (μ := μ) hherm)
    with hmudef
  have hμnn : 0 ≤ μmin := chernoff_mu_min_nonneg (μ := μ) hmeas hherm hmin hmax
  have hcard1 : (1 : ℝ) ≤ (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hPle : ∀ S : Set Ω, μ.real S ≤ 1 := fun S => by
    have h := MeasureTheory.measureReal_mono (μ := μ) (Set.subset_univ S)
    rwa [MeasureTheory.probReal_univ] at h
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · rw [← hL0, mul_zero, div_zero, Real.exp_zero, mul_one]
    exact (hPle _).trans hcard1
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hR : ∀ k ω, ‖X k ω‖ ≤ (fun _ : ι => L) k := fun k ω =>
    l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · -- `t = 0`: master bound directly at `θ = −1/L`
    have hθ' : -(1 : ℝ) / L < 0 :=
      div_neg_of_neg_of_pos (by norm_num) hLpos
    have h1 := master_tail_lower (μ := μ) hmeas hherm hR hind
      ((0 : ℝ) * μmin) hθ'
    have h2 := chernoff_cgf_trace_bound_lower (μ := μ) hmeas hherm hmin hmax
      hLpos hθ'
    rw [← ht0]
    refine h1.trans ?_
    have hexp0 : Real.exp (-(-(1 : ℝ) / L) * ((0 : ℝ) * μmin)) = 1 := by
      rw [show -(-(1 : ℝ) / L) * ((0 : ℝ) * μmin) = 0 from by ring,
        Real.exp_zero]
    rw [hexp0, one_mul]
    refine h2.trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have hg : gChernoff (-(1 : ℝ) / L) L = (Real.exp (-1) - 1) / L := by
      rw [gChernoff, div_mul_cancel₀ _ hLne]
    have hehalf : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.exp_neg]
      have h2e : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith
      calc (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ :=
            (inv_le_inv₀ (by positivity) (by norm_num)).mpr h2e
      _ = 1 / 2 := by norm_num
    rw [hg, show -((1 : ℝ) - 0) ^ 2 * μmin / (2 * L) =
      (-(1 : ℝ) / 2) * μmin / L from by ring, div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right hLpos]
    refine mul_le_mul_of_nonneg_right ?_ hμnn
    linarith
  · -- `t > 0`: exact lower tail at `ε = 1 − t`, then the entropy inequality
    have hε : (0 : ℝ) ≤ 1 - t := by linarith
    have hε1 : 1 - t < 1 := by linarith
    have h := matrix_chernoff_tail_lower (μ := μ) hmeas hherm hmin hmax hL hind
      hε hε1
    rw [show (1 : ℝ) - (1 - t) = t from by ring] at h
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hexp_target : (Real.exp (-(1 - t) ^ 2 / 2)) ^ (μmin / L) =
        Real.exp (-(1 - t) ^ 2 * μmin / (2 * L)) := by
      rw [← Real.exp_mul]
      congr 1
      field_simp
    have hbpos : (0 : ℝ) < Real.exp (-(1 - t)) / t ^ (t : ℝ) :=
      div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos htpos _)
    have hble : Real.exp (-(1 - t)) / t ^ (t : ℝ) ≤
        Real.exp (-(1 - t) ^ 2 / 2) := by
      rw [show Real.exp (-(1 - t)) / t ^ (t : ℝ) =
        Real.exp (Real.log (Real.exp (-(1 - t)) / t ^ (t : ℝ))) from
        (Real.exp_log hbpos).symm]
      refine Real.exp_le_exp.mpr ?_
      rw [Real.log_div (Real.exp_pos _).ne'
        (Real.rpow_pos_of_pos htpos _).ne', Real.log_exp,
        Real.log_rpow htpos]
      have hent := entropy_lower_bound hε hε1
      rw [show (1 : ℝ) - (1 - t) = t from by ring] at hent
      nlinarith [hent]
    calc (Real.exp (-(1 - t)) / t ^ (t : ℝ)) ^ (μmin / L)
        ≤ (Real.exp (-(1 - t) ^ 2 / 2)) ^ (μmin / L) :=
          Real.rpow_le_rpow hbpos.le hble (div_nonneg hμnn hL)
    _ = Real.exp (-(1 - t) ^ 2 * μmin / (2 * L)) := hexp_target

/-- **Book §5.1.1, second weakened tail display** (C5-03):
`P(λ_max(Y) ≥ t·μ_max) ≤ d·(e/t)^{t·μ_max/L}` for `t ≥ e` — "the upper tail of
`λ_max(Y)` decays faster than that of an exponential random variable with mean
`L/μ_max`." Explicit source declaration. -/
theorem matrix_chernoff_tail_upper_exponential
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) (hL : 0 ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) {t : ℝ} (ht : Real.exp 1 ≤ t) :
    μ.real {ω | t * lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) ≤
        lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω))} ≤
      (Fintype.card n : ℝ) * (Real.exp 1 / t) ^
        (t * lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) / L) := by
  classical
  set μmax : ℝ := lambdaMax (isHermitian_sum_expectation (μ := μ) hherm)
    with hmudef
  have hμnn : 0 ≤ μmax := chernoff_mu_max_nonneg (μ := μ) hmeas hherm hmin hmax
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos 1) ht
  have hε : (0 : ℝ) ≤ t - 1 := by
    have h1 : (1 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    linarith
  have h := matrix_chernoff_tail_upper (μ := μ) hmeas hherm hmin hmax hL hind hε
  rw [show (1 : ℝ) + (t - 1) = t from by ring] at h
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- base comparison `e^{t−1}/t^t ≤ (e/t)^t`, then collapse the double power
  have hbnn : (0 : ℝ) ≤ Real.exp (t - 1) / t ^ (t : ℝ) := by positivity
  have hbase : Real.exp (t - 1) / t ^ (t : ℝ) ≤ (Real.exp 1 / t) ^ (t : ℝ) := by
    rw [Real.div_rpow (Real.exp_pos 1).le htpos.le, Real.exp_one_rpow]
    gcongr
    · linarith
  calc (Real.exp (t - 1) / t ^ (t : ℝ)) ^ (μmax / L)
      ≤ ((Real.exp 1 / t) ^ (t : ℝ)) ^ (μmax / L) :=
        Real.rpow_le_rpow hbnn hbase (div_nonneg hμnn hL)
  _ = (Real.exp 1 / t) ^ (t * μmax / L) := by
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Real.exp 1 / t)]
      congr 1
      ring

end WeakenedTails

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Related results and optimality of the matrix Chernoff bounds (Tropp §5.1.1–§5.1.2)

* `matrix_rosenthal` — **Book (5.1.9)** (C5-04), the matrix
  Rosenthal inequality
  `𝔼λ_max(Y) ≤ 2μ_max + 8e·(𝔼 max_k λ_max(X_k))·log d`;
* `expectation_max_lambdaMax_le` — the remark after **Book (5.1.9)** (C5-05): the
  uniform bound `L` always dominates `𝔼 max_k λ_max(X_k)`;
* the §5.1.2 upper-optimality facts (C5-06):
  `lambdaMax_expectation_ge_mu` (Jensen), `lambdaMax_add_posSemidef_ge`
  (`λ_max(A+H) ≥ λ_max(A)` for psd `H`),
  `expectation_max_le_expectation_lambdaMax`
  (`𝔼 max_k λ_max(X_k) ≤ 𝔼λ_max(Y)`), and their average
  `rosenthal_lower_two_sided` — the lower half of **Book (5.1.10)**; the upper
  half `rosenthal_upper_two_sided` is the Rosenthal bound itself;
* `expectation_lambdaMin_le_mu` — the §5.1.2 lower-optimality Jensen fact
  (C5-08): `𝔼λ_min(Y) ≤ μ_min`;
* `bernoulli_diagonal_example` — the §5.1.2 display
  `𝔼λ_max(Y_N) ≤ 1.72 + log d` for the diagonal Bernoulli family (C5-07);
* `coupon_collector_lower_instance` — the §5.1.2 display
  `𝔼λ_min(Y_n) ≥ ((1−e^{−θ})/θ)·n − θ⁻¹·d·log d` for an iid family with
  `𝔼X = I` and `λ_max ≤ d` (C5-08).

-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsProbabilityMeasure μ] [Nonempty n] [Nonempty ι]
variable {X : ι → Ω → Matrix n n ℂ} {L : ℝ}

section MaxFacts

/-- Lean implementation helper: measurability and integrability of
`ω ↦ max_k λ_max(X_k ω)` under the standing bounds. -/
lemma integrable_sup_lambdaMax
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) :
    Integrable (fun ω => Finset.univ.sup' Finset.univ_nonempty
      (fun k => lambdaMax (hherm k ω))) μ := by
  have hbd : ∀ k ω, ‖X k ω‖ ≤ L := fun k ω =>
    l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
  refine Integrable.of_bound ?_ L ?_
  · have hm := Finset.measurable_sup' (s := (Finset.univ : Finset ι))
      Finset.univ_nonempty (f := fun k (ω : Ω) => lambdaMax (hherm k ω))
      (fun k _ => measurable_lambdaMax (hmeas k) (hherm k) (hbd k))
    have heq : (Finset.univ.sup' Finset.univ_nonempty
        (fun k (ω : Ω) => lambdaMax (hherm k ω))) =
        fun ω => Finset.univ.sup' Finset.univ_nonempty
          (fun k => lambdaMax (hherm k ω)) := by
      funext ω
      exact Finset.sup'_apply _ _ _
    rw [heq] at hm
    exact hm.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · obtain ⟨k⟩ := (inferInstance : Nonempty ι)
      have h1 : -L ≤ lambdaMax (hherm k ω) := by
        have := (hmin k ω).trans ((lambdaMin_le_eigenvalues (hherm k ω)
          (Classical.arbitrary n)).trans (eigenvalues_le_lambdaMax (hherm k ω)
            (Classical.arbitrary n)))
        have hL0 : 0 ≤ L := this.trans (hmax k ω)
        linarith
      exact h1.trans (Finset.le_sup' (fun j => lambdaMax (hherm j ω))
        (Finset.mem_univ k))
    · exact Finset.sup'_le _ _ fun k _ => hmax k ω

/-- **Book §5.1.1 remark after (5.1.9)** (C5-05): "the uniform bound `L` …
always exceeds the large parenthesis" — `𝔼 max_k λ_max(X_k) ≤ L`.  Implicit
source declaration. -/
theorem expectation_max_lambdaMax_le
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) :
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty
      (fun k => lambdaMax (hherm k ω)) ∂μ ≤ L := by
  calc (∫ ω, Finset.univ.sup' Finset.univ_nonempty
        (fun k => lambdaMax (hherm k ω)) ∂μ)
      ≤ ∫ _x, L ∂μ := by
        refine MeasureTheory.integral_mono
          (integrable_sup_lambdaMax (μ := μ) hmeas hherm hmin hmax)
          (integrable_const _) fun ω => ?_
        exact Finset.sup'_le _ _ fun k _ => hmax k ω
  _ = L := by
      rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]

end MaxFacts

section UpperOptimality

/-- **Book §5.1.2** (C5-06): `λ_max(A + H) ≥ λ_max(A)` whenever `H` is positive
semidefinite.  Implicit source declaration ("We have used the fact that …"). -/
lemma lambdaMax_add_posSemidef_ge {A H : Matrix n n ℂ} (hA : A.IsHermitian)
    (hH : H.PosSemidef) (hAH : (A + H).IsHermitian) :
    lambdaMax hA ≤ lambdaMax hAH := by
  obtain ⟨u, hu, hval⟩ := exists_unit_rayleigh_eq_lambdaMax hA
  rw [← hval]
  have h1 : rayleigh (A + H) u = rayleigh A u + rayleigh H u := by
    show ((star u) ⬝ᵥ ((A + H) *ᵥ u)).re = _
    rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
    rfl
  have h2 : 0 ≤ rayleigh H u := hH.re_dotProduct_nonneg u
  have h3 := rayleigh_le_lambdaMax_of_unit hAH hu
  rw [h1] at h3
  linarith

/-- **Book §5.1.2** (C5-06, Jensen half): `μ_max ≤ 𝔼 λ_max(Y)` — "The
appearance of `μ_max` … is a consequence of Jensen's inequality.  Indeed, the
maximum eigenvalue is convex."  Explicit source declaration (displayed). -/
theorem lambdaMax_expectation_ge_mu
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) :
    lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) ≤
      ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ := by
  have hint : ∀ k, MIntegrable (X k) μ := fun k =>
    mintegrable_of_eigenvalue_bounds (hmeas k) (hherm k) (hmin k) (hmax k)
  have hYint : MIntegrable (fun ω => ∑ k, X k ω) μ := by
    intro i j
    have h1 : (fun ω => (∑ k, X k ω) i j) = fun ω => ∑ k, X k ω i j := by
      funext ω
      rw [Matrix.sum_apply]
    rw [h1]
    exact integrable_finset_sum _ fun k _ => hint k i j
  have hYherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ ∑ _k : ι, L := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
    _ ≤ ∑ _k, L := Finset.sum_le_sum fun k _ =>
        l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
  have hlamint : Integrable (fun ω => lambdaMax (hYherm ω)) μ :=
    integrable_lambdaMax (measurable_matsum Finset.univ hmeas) hYherm hYbd
  have hEherm : (expectation μ (fun ω => ∑ k, X k ω)).IsHermitian :=
    isHermitian_expectation (Filter.Eventually.of_forall hYherm)
  have h := lambdaMax_expectation_le hYint hYherm hEherm hlamint
  rwa [lambdaMax_congr (expectation_matsum_eq hint)
    hEherm (isHermitian_sum_expectation (μ := μ) hherm)] at h

/-- **Book §5.1.2** (C5-06): `𝔼 max_k λ_max(X_k) ≤ 𝔼 λ_max(Y)` — "apply the
fact that the summands `X_k` are positive semidefinite".  Explicit source
declaration (displayed).

**Author note.** This uniformly bounded form is retained for compatibility;
see `expectation_max_le_expectation_lambdaMax_of_integrable` for the
source-faithful a.e.-PSD, integrable counterpart. -/
theorem expectation_max_le_expectation_lambdaMax
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) :
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty
        (fun k => lambdaMax (hherm k ω)) ∂μ ≤
      ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ := by
  have hYherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ ∑ _k : ι, L := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
    _ ≤ ∑ _k, L := Finset.sum_le_sum fun k _ =>
        l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
  refine MeasureTheory.integral_mono
    (integrable_sup_lambdaMax (μ := μ) hmeas hherm hmin hmax)
    (integrable_lambdaMax (measurable_matsum Finset.univ hmeas) hYherm hYbd)
    fun ω => ?_
  refine Finset.sup'_le _ _ fun k _ => ?_
  -- `Σ X = X_k + Σ_{j≠k} X_j` with the second summand psd
  have hsplit : (∑ j, X j ω) = X k ω + ∑ j ∈ Finset.univ.erase k, X j ω :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
  have hrest : (∑ j ∈ Finset.univ.erase k, X j ω).PosSemidef :=
    posSemidef_matsum _ fun j =>
      posSemidef_of_lambdaMin_nonneg (hherm j ω) (hmin j ω)
  have hAH : (X k ω + ∑ j ∈ Finset.univ.erase k, X j ω).IsHermitian := by
    rw [← hsplit]
    exact hYherm ω
  have h := lambdaMax_add_posSemidef_ge (hherm k ω) hrest hAH
  rwa [← lambdaMax_congr hsplit (hYherm ω) hAH] at h

/-- **Book (5.1.10)** (§5.1.2, C5-06), lower half:
`(1/2)·[μ_max + 𝔼 max_k λ_max(X_k)] ≤ 𝔼 λ_max(Y)` — "Average the last two
displays to develop the left-hand side." Explicit source declaration.

**Author note.** Lean makes the source's unspecified lower constant explicit
as `1/2`. -/
theorem rosenthal_lower_two_sided
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) :
    (1 / 2 : ℝ) * (lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) +
        ∫ ω, Finset.univ.sup' Finset.univ_nonempty
          (fun k => lambdaMax (hherm k ω)) ∂μ) ≤
      ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ := by
  have h1 := lambdaMax_expectation_ge_mu (μ := μ) hmeas hherm hmin hmax
  have h2 := expectation_max_le_expectation_lambdaMax (μ := μ) hmeas hherm hmin hmax
  linarith

/-- **Book (5.1.9)** (§5.1.1, C5-04): the matrix Rosenthal inequality stated
through [CGT12, Theorem A.1].

**Author note.** The auxiliary argument proves the stronger coefficient
`8 * log d`; this theorem retains the Book's coefficient `8 * e * log d`. -/
theorem matrix_rosenthal
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hint : ∀ k, MIntegrable (X k) μ)
    (hind : ProbabilityTheory.iIndepFun X μ)
    (hsupint : Integrable (fun ω => Finset.univ.sup' Finset.univ_nonempty
      (fun k => lambdaMax (hherm k ω))) μ)
    (hYint : Integrable (fun ω => lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hherm k ω))) μ) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ ≤
      2 * lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) +
        8 * Real.exp 1 *
          (∫ ω, Finset.univ.sup' Finset.univ_nonempty
            (fun k => lambdaMax (hherm k ω)) ∂μ) * Real.log (Fintype.card n) := by
  exact matrix_rosenthal_aux hmeas hherm hmin hint hind hsupint hYint

/-- **Book (5.1.10)**, upper half — "The right-hand side of (5.1.10) is
obviously just (5.1.9)" (with `Const = 8e`). -/
theorem rosenthal_upper_two_sided
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L)
    (hind : ProbabilityTheory.iIndepFun X μ) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ ≤
      8 * Real.exp 1 *
        (lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) +
          (∫ ω, Finset.univ.sup' Finset.univ_nonempty
            (fun k => lambdaMax (hherm k ω)) ∂μ) * Real.log (Fintype.card n)) := by
  have hint : ∀ k, MIntegrable (X k) μ := fun k =>
    mintegrable_of_eigenvalue_bounds (hmeas k) (hherm k) (hmin k) (hmax k)
  have hYherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ ∑ _k : ι, L := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
    _ ≤ ∑ _k, L := Finset.sum_le_sum fun k _ =>
        l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
  have h := matrix_rosenthal (μ := μ) hmeas hherm hmin hint hind
    (integrable_sup_lambdaMax (μ := μ) hmeas hherm hmin hmax)
    (integrable_lambdaMax (measurable_matsum Finset.univ hmeas) hYherm hYbd)
  refine h.trans ?_
  have hμ := chernoff_mu_max_nonneg (μ := μ) hmeas hherm hmin hmax
  have hsupnn : 0 ≤ ∫ ω, Finset.univ.sup' Finset.univ_nonempty
      (fun k => lambdaMax (hherm k ω)) ∂μ := by
    refine MeasureTheory.integral_nonneg fun ω => ?_
    obtain ⟨k⟩ := (inferInstance : Nonempty ι)
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ k))
    exact (hmin k ω).trans ((lambdaMin_le_eigenvalues (hherm k ω)
      (Classical.arbitrary n)).trans (eigenvalues_le_lambdaMax (hherm k ω)
        (Classical.arbitrary n)))
  have hlognn : (0 : ℝ) ≤ Real.log (Fintype.card n) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have he : (2 : ℝ) ≤ 8 * Real.exp 1 := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    nlinarith
  nlinarith [mul_nonneg hsupnn hlognn]

end UpperOptimality

section LowerOptimality

/-- **Book §5.1.2** (C5-08): `𝔼 λ_min(Y) ≤ μ_min` — "This estimate is a
consequence of Jensen's inequality and the concavity of the minimum
eigenvalue."  Explicit source declaration (displayed). -/
theorem expectation_lambdaMin_le_mu
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ L) :
    ∫ ω, lambdaMin (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ ≤
      lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) := by
  have hint : ∀ k, MIntegrable (X k) μ := fun k =>
    mintegrable_of_eigenvalue_bounds (hmeas k) (hherm k) (hmin k) (hmax k)
  have hYint : MIntegrable (fun ω => ∑ k, X k ω) μ := by
    intro i j
    have h1 : (fun ω => (∑ k, X k ω) i j) = fun ω => ∑ k, X k ω i j := by
      funext ω
      rw [Matrix.sum_apply]
    rw [h1]
    exact integrable_finset_sum _ fun k _ => hint k i j
  have hYherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ ∑ _k : ι, L := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
    _ ≤ ∑ _k, L := Finset.sum_le_sum fun k _ =>
        l2_opNorm_le_of_eigenvalue_bounds (hherm k ω) (hmin k ω) (hmax k ω)
  have hlamint : Integrable (fun ω => lambdaMin (hYherm ω)) μ :=
    integrable_lambdaMin (measurable_matsum Finset.univ hmeas) hYherm hYbd
  have hEherm : (expectation μ (fun ω => ∑ k, X k ω)).IsHermitian :=
    isHermitian_expectation (Filter.Eventually.of_forall hYherm)
  have h := expectation_lambdaMin_le hYint hYherm hEherm hlamint
  rwa [lambdaMin_congr (expectation_matsum_eq hint)
    hEherm (isHermitian_sum_expectation (μ := μ) hherm)] at h

end LowerOptimality

section Examples

/-- Lean implementation helper: `λ_max(I) = 1`. -/
lemma lambdaMax_one : lambdaMax (Matrix.isHermitian_one (n := n) (α := ℂ)) = 1 := by
  have hpsd : (1 : Matrix n n ℂ).PosSemidef := Matrix.PosDef.one.posSemidef
  have h := posSemidef_l2_opNorm_eq_lambdaMax hpsd
  rw [l2_opNorm_one] at h
  exact h.symm

/-- Lean implementation helper: the diagonal Bernoulli summands
`δ·E_kk` satisfy the Chernoff hypotheses with `L = 1`. -/
lemma bernoulli_single_eigenvalue_bounds {δ : ℝ} (hδ : δ = 0 ∨ δ = 1) (k : n)
    (hherm : (δ • Matrix.single k k (1 : ℂ)).IsHermitian) :
    0 ≤ lambdaMin hherm ∧ lambdaMax hherm ≤ 1 := by
  have hpsd : (δ • Matrix.single k k (1 : ℂ)).PosSemidef := by
    rcases hδ with h | h <;> subst h
    · rw [zero_smul]
      exact Matrix.PosSemidef.zero
    · rw [one_smul, show Matrix.single k k (1 : ℂ) =
        Matrix.diagonal (Pi.single k 1) from ?_]
      · refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
        by_cases hik : k = i
        · subst hik
          rw [Pi.single_eq_same]
          norm_num
        · rw [Pi.single_eq_of_ne (Ne.symm hik)]
      · ext a b
        rw [Matrix.single_apply, Matrix.diagonal_apply]
        by_cases hab : a = b
        · subst hab
          by_cases hka : k = a
          · subst hka
            rw [if_pos ⟨rfl, rfl⟩, if_pos rfl, Pi.single_eq_same]
          · rw [if_neg (fun h => hka h.1), if_pos rfl,
            Pi.single_eq_of_ne (Ne.symm hka)]
        · rw [if_neg (fun h => hab (h.1.symm.trans h.2)), if_neg hab]
  have hle : δ • Matrix.single k k (1 : ℂ) ≤ 1 := by
    rcases hδ with h | h <;> subst h
    · rw [zero_smul, Matrix.le_iff, sub_zero]
      exact Matrix.PosDef.one.posSemidef
    · rw [one_smul, Matrix.le_iff]
      rw [show (1 : Matrix n n ℂ) - Matrix.single k k 1 =
        Matrix.diagonal (fun i => if k = i then 0 else 1) from ?_]
      · refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
        by_cases hik : k = i
        · rw [if_pos hik]
        · rw [if_neg hik]
          norm_num
      · ext a b
        rw [Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply,
          Matrix.diagonal_apply]
        by_cases hab : a = b
        · subst hab
          by_cases hka : k = a
          · subst hka
            rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, if_pos rfl, if_pos rfl]
            norm_num
          · rw [if_pos rfl, if_neg (fun h => hka h.1), if_pos rfl, if_neg hka]
            norm_num
        · rw [if_neg hab, if_neg (fun h => hab (h.1.symm.trans h.2)), if_neg hab]
          norm_num
  constructor
  · exact le_lambdaMin _ fun i => hpsd.eigenvalues_nonneg i
  · calc lambdaMax hherm ≤ lambdaMax (Matrix.isHermitian_one (n := n) (α := ℂ)) :=
        lambdaMax_le_of_loewner_le _ _ hle
    _ = 1 := lambdaMax_one

/-- **Book §5.1.2 display** (C5-07): the diagonal Bernoulli example — for
`Y_N = Σ_{i<N} Σ_{k<d} δ_ik E_kk` with independent BERNOULLI(1/N) modulators,
`𝔼 λ_max(Y_N) ≤ 1.72 + log d`.  Explicit source declaration ("An easy
application of **Book (5.1.8)** delivers …"). -/
theorem bernoulli_diagonal_example {N : ℕ} [NeZero N]
    {δ : Fin N × n → Ω → ℝ}
    (hmeas : ∀ p, Measurable (δ p))
    (hlaw : ∀ p, IsBernoulli ((N : ℝ)⁻¹) (δ p) μ)
    (hrange : ∀ p ω, δ p ω = 0 ∨ δ p ω = 1)
    (hind : ProbabilityTheory.iIndepFun δ μ)
    (hherm : ∀ (p : Fin N × n) ω,
      ((fun p ω => δ p ω • Matrix.single p.2 p.2 (1 : ℂ)) p ω).IsHermitian) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun p => hherm p ω)) ∂μ ≤
      1.72 + Real.log (Fintype.card n) := by
  classical
  set X : Fin N × n → Ω → Matrix n n ℂ :=
    fun p ω => δ p ω • Matrix.single p.2 p.2 (1 : ℂ) with hXdef
  have hXmeas : ∀ p, Measurable (X p) := fun p => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => δ p ω • Matrix.single p.2 p.2 (1 : ℂ) i j
    exact (hmeas p).smul_const _
  have hXmin : ∀ p ω, 0 ≤ lambdaMin (hherm p ω) := fun p ω =>
    (bernoulli_single_eigenvalue_bounds (hrange p ω) p.2 (hherm p ω)).1
  have hXmax : ∀ p ω, lambdaMax (hherm p ω) ≤ 1 := fun p ω =>
    (bernoulli_single_eigenvalue_bounds (hrange p ω) p.2 (hherm p ω)).2
  have hXind : ProbabilityTheory.iIndepFun X μ := by
    refine hind.comp (fun p s => s • Matrix.single p.2 p.2 (1 : ℂ)) fun p => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun s : ℝ => s • Matrix.single p.2 p.2 (1 : ℂ) i j
    exact measurable_id.smul_const _
  have h := matrix_chernoff_expectation_upper_simple (μ := μ) hXmeas hherm
    hXmin hXmax zero_le_one hXind
  refine h.trans ?_
  -- `Σ_p 𝔼X_p = I`, so `μ_max = 1`
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hp1 : (N : ℝ)⁻¹ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [inv_le_one_iff₀]
      right
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hEX : ∀ p : Fin N × n, expectation μ (X p) =
      (N : ℝ)⁻¹ • Matrix.single p.2 p.2 (1 : ℂ) := by
    intro p
    ext i j
    rw [expectation_apply, Matrix.smul_apply]
    have h1 : (fun ω => X p ω i j) =
        fun ω => δ p ω • Matrix.single p.2 p.2 (1 : ℂ) i j := by
      funext ω
      show (δ p ω • Matrix.single p.2 p.2 (1 : ℂ)) i j = _
      rw [Matrix.smul_apply]
    rw [h1]
    have h2 : ∫ ω, δ p ω • Matrix.single p.2 p.2 (1 : ℂ) i j ∂μ =
        (∫ ω, δ p ω ∂μ) • Matrix.single p.2 p.2 (1 : ℂ) i j :=
      integral_smul_const _ _
    rw [h2, integral_id_isBernoulli hp1 (hmeas p) (hlaw p)]
  have hsum : (∑ p : Fin N × n, expectation μ (X p)) = 1 := by
    rw [Finset.sum_congr rfl fun p _ => hEX p]
    rw [show (Finset.univ : Finset (Fin N × n)) = Finset.univ ×ˢ Finset.univ from
      (Finset.univ_product_univ).symm, Finset.sum_product]
    have h1 : ∀ i : Fin N, (∑ k : n, (N : ℝ)⁻¹ • Matrix.single k k (1 : ℂ)) =
        (N : ℝ)⁻¹ • (1 : Matrix n n ℂ) := by
      intro i
      rw [← Finset.smul_sum, sum_single_diag_one]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt hNpos), one_smul]
  have hmu : lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) = 1 := by
    rw [lambdaMax_congr hsum (isHermitian_sum_expectation (μ := μ) hherm)
      Matrix.isHermitian_one]
    exact lambdaMax_one
  rw [hmu]
  norm_num

/-- **Book §5.1.2 display** (C5-08): the coupon-collector lower instance — for
an iid psd family with `𝔼X_k = I` and eigenvalues in `[0, d]`,
`𝔼 λ_min(Y_n) ≥ ((1−e^{−θ})/θ)·n − θ⁻¹·d·log d`.  Explicit source declaration
("The lower Chernoff bound **Book (5.1.3)** implies that …").

**Author note.** The Lean statement needs only independence, the individual
mean identities, and the common eigenvalue bound; identical distribution is
not required. -/
theorem coupon_collector_lower_instance
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k ω, 0 ≤ lambdaMin (hherm k ω))
    (hmax : ∀ k ω, lambdaMax (hherm k ω) ≤ (Fintype.card n : ℝ))
    (hE : ∀ k, expectation μ (X k) = 1)
    (hind : ProbabilityTheory.iIndepFun X μ) {θ : ℝ} (hθ : 0 < θ) :
    (1 - Real.exp (-θ)) / θ * (Fintype.card ι) -
        θ⁻¹ * (Fintype.card n) * Real.log (Fintype.card n) ≤
      ∫ ω, lambdaMin (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ := by
  have h := matrix_chernoff_expectation_lower (μ := μ) hmeas hherm hmin hmax
    (by positivity) hind hθ
  refine le_trans (le_of_eq ?_) h
  -- `μ_min = λ_min(Σ_k I) = card ι`
  have hsum : (∑ k : ι, expectation μ (X k)) =
      (Fintype.card ι : ℝ) • (1 : Matrix n n ℂ) := by
    rw [Finset.sum_congr rfl fun k _ => hE k, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
  have hmu : lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) =
      (Fintype.card ι : ℝ) := by
    have hcast : ((Fintype.card ι : ℝ)) • (1 : Matrix n n ℂ) =
        (((Fintype.card ι : ℝ) : ℝ)) • 1 := rfl
    rw [lambdaMin_congr hsum (isHermitian_sum_expectation (μ := μ) hherm)
      (isHermitian_real_smul Matrix.isHermitian_one _)]
    rw [lambdaMin_smul_nonneg Matrix.isHermitian_one (by positivity)
      (isHermitian_real_smul Matrix.isHermitian_one _)]
    have hone : lambdaMin (Matrix.isHermitian_one (n := n) (α := ℂ)) = 1 := by
      obtain ⟨u, hu, hval⟩ := exists_unit_rayleigh_eq_lambdaMin
        (Matrix.isHermitian_one (n := n) (α := ℂ))
      rw [← hval]
      show ((star u) ⬝ᵥ ((1 : Matrix n n ℂ) *ᵥ u)).re = 1
      rw [Matrix.one_mulVec, dotProduct_star_self_eq, hu]
      norm_num
    rw [hone, mul_one]
  rw [hmu]

end Examples

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Example: a random column submatrix of a fixed matrix (Tropp §5.2.1)

* `columnSubmatrix` — the random column-sampling model
  `Z = Σ_k δ_k · b_{:k} e_k*` (each column kept independently with probability
  `q`; the book's parametrization is `q = p/n`), realized as
  `Σ_k δ_k · (B·E_kk)`;
* `columnSubmatrix_gram` — the §5.2.1 analysis display
  `Y = ZZ* = Σ_k δ_k · b_{:k} b_{:k}*` (uses `δ_k² = δ_k`);
* `expectation_column_gram` — `𝔼Y = q·BB*`;
* `column_submatrix_upper`/`column_submatrix_lower` — **Book (5.2.1)**:
  `𝔼 σ₁(Z)² ≤ 1.72·q·σ₁(B)² + (log d)·max_k ‖b_{:k}‖²` and
  `𝔼 σ_d(Z)² ≥ 0.63·q·σ_d(B)² − (log d)·max_k ‖b_{:k}‖²`,
  rendered through the book's own identifications
  `σ₁(Z)² = λ_max(ZZ*)`, `σ_d(Z)² = λ_min(ZZ*)` (and
  `σ₁(B)² = λ_max(BB*)`, `σ_d(B)² = λ_min(BB*)`); the norm form
  `‖Z‖² = λ_max(ZZ*)` is supplied by `sq_norm_eq_lambdaMax_gram`.

-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [IsProbabilityMeasure μ]

section Model

/-- **Book §5.2.1** (C5-09): the random column submatrix
`Z = Σ_k δ_k · b_{:k} e_k*` — "we include each column independently with
probability `p/n` … we just zero them out."  The rank-one term
`b_{:k} e_k*` is realized as `B · E_kk` (the matrix that keeps column `k` of
`B` and zeroes the others).  Explicit source declaration. -/
noncomputable def columnSubmatrix (B : Matrix m n ℂ) (δ : n → Ω → ℝ) (ω : Ω) :
    Matrix m n ℂ :=
  ∑ k, δ k ω • (B * Matrix.single k k (1 : ℂ))

/-- Lean implementation helper: the column Gram summand `b_{:k} b_{:k}*`,
realized as `B · E_kk · B*`. -/
noncomputable def colGram (B : Matrix m n ℂ) (k : n) : Matrix m m ℂ :=
  B * Matrix.single k k (1 : ℂ) * Bᴴ

/-- Lean implementation helper: `(B·E_kk)·(B·E_ll)* = 0` for `k ≠ l` and
`= B·E_kk·B*` for `k = l`. -/
lemma colPiece_mul_conjTranspose (B : Matrix m n ℂ) (k l : n) :
    (B * Matrix.single k k (1 : ℂ)) * (B * Matrix.single l l (1 : ℂ))ᴴ =
      if k = l then colGram B k else 0 := by
  rw [Matrix.conjTranspose_mul, conjTranspose_single]
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, colGram]
    calc B * Matrix.single k k (1 : ℂ) * (Matrix.single k k (1 : ℂ) * Bᴴ)
        = B * (Matrix.single k k (1 : ℂ) * Matrix.single k k (1 : ℂ)) * Bᴴ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = B * Matrix.single k k (1 : ℂ) * Bᴴ := by
        rw [Matrix.single_mul_single_same, one_mul]
  · rw [if_neg hkl]
    calc B * Matrix.single k k (1 : ℂ) * (Matrix.single l l (1 : ℂ) * Bᴴ)
        = B * (Matrix.single k k (1 : ℂ) * Matrix.single l l (1 : ℂ)) * Bᴴ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = 0 := by
        rw [Matrix.single_mul_single_of_ne (h := hkl)]
        simp

/-- **Book §5.2.1 analysis display** (C5-09): `Y = ZZ* = Σ_k δ_k b_{:k}b_{:k}*`
— "Note that `δ_k² = δ_k` because `δ_k` only takes the values zero and one."
Explicit source declaration. -/
theorem columnSubmatrix_gram (B : Matrix m n ℂ) {δ : n → Ω → ℝ}
    (hrange : ∀ k ω, δ k ω = 0 ∨ δ k ω = 1) (ω : Ω) :
    columnSubmatrix B δ ω * (columnSubmatrix B δ ω)ᴴ =
      ∑ k, δ k ω • colGram B k := by
  classical
  rw [columnSubmatrix, Matrix.conjTranspose_sum, Matrix.sum_mul]
  have h1 : ∀ j, (δ j ω • (B * Matrix.single j j (1 : ℂ))) *
      (∑ k, (δ k ω • (B * Matrix.single k k (1 : ℂ)))ᴴ) = δ j ω • colGram B j := by
    intro j
    rw [Matrix.mul_sum]
    have h2 : ∀ k, (δ j ω • (B * Matrix.single j j (1 : ℂ))) *
        (δ k ω • (B * Matrix.single k k (1 : ℂ)))ᴴ =
        if j = k then (δ j ω * δ k ω) • colGram B j else 0 := by
      intro k
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, colPiece_mul_conjTranspose]
      by_cases hjk : j = k
      · rw [if_pos hjk, if_pos hjk]
      · rw [if_neg hjk, if_neg hjk, smul_zero]
    rw [Finset.sum_congr rfl fun k _ => h2 k, Finset.sum_ite_eq
      Finset.univ j (fun k => (δ j ω * δ k ω) • colGram B j)]
    rw [if_pos (Finset.mem_univ j)]
    have hsq : δ j ω * δ j ω = δ j ω := by
      rcases hrange j ω with h | h <;> rw [h] <;> ring
    rw [hsq]
  exact Finset.sum_congr rfl fun j _ => h1 j

/-- Lean implementation helper: the Gram summands are psd
(`b_{:k}b_{:k}* = (B·E_kk)(B·E_kk)*`). -/
lemma posSemidef_colGram (B : Matrix m n ℂ) (k : n) : (colGram B k).PosSemidef := by
  have h := colPiece_mul_conjTranspose B k k
  rw [if_pos rfl] at h
  rw [← h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Lean implementation helper: the squared column norms of `B`. -/
noncomputable def colNormSq (B : Matrix m n ℂ) (k : n) : ℝ := ∑ i, ‖B i k‖ ^ 2

/-- Lean implementation helper: nonnegativity of a squared column norm. -/
lemma colNormSq_nonneg (B : Matrix m n ℂ) (k : n) : 0 ≤ colNormSq B k :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Lean implementation helper: the Gram summand is the outer product of the
`k`-th column, entrywise. -/
lemma colGram_apply (B : Matrix m n ℂ) (k : n) (i j : m) :
    colGram B k i j = B i k * star (B j k) := by
  rw [colGram]
  have h1 : (B * Matrix.single k k (1 : ℂ)) i k = B i k := by
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, mul_one]
    · intro l _ hlk
      rw [Matrix.single_apply, if_neg (fun h => hlk h.1.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [Matrix.conjTranspose_apply, h1]
  · intro l _ hlk
    have h2 : (B * Matrix.single k k (1 : ℂ)) i l = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [Matrix.single_apply,
        if_neg (fun h : k = a ∧ k = l => hlk h.2.symm), mul_zero]
    rw [h2, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- **Book §5.2.1** (C5-09): `‖δ_k b_{:k}b_{:k}*‖ ≤ L = max_k ‖b_{:k}‖²`.
The Gram summand norm is at most the squared column norm.  Implicit source
declaration ("observe that …"). -/
lemma l2_opNorm_colGram_le (B : Matrix m n ℂ) (k : n) :
    ‖colGram B k‖ ≤ colNormSq B k := by
  set v : m → ℂ := fun i => B i k with hv
  refine l2_opNorm_le_of_forall_dotProduct _ (colNormSq_nonneg B k) fun u w => ?_
  have hMw : (colGram B k) *ᵥ w = fun i => v i * (star v ⬝ᵥ w) := by
    funext i
    show ∑ j, colGram B k i j * w j = _
    rw [show (∑ j, colGram B k i j * w j) =
      ∑ j, v i * (star (v j) * w j) from Finset.sum_congr rfl fun j _ => by
        rw [colGram_apply]
        ring]
    rw [← Finset.mul_sum]
    rfl
  rw [hMw]
  have hdot : star u ⬝ᵥ (fun i => v i * (star v ⬝ᵥ w)) =
      (star u ⬝ᵥ v) * (star v ⬝ᵥ w) := by
    show (∑ i, star (u i) * (v i * (star v ⬝ᵥ w))) = _
    rw [show (∑ i, star (u i) * (v i * (star v ⬝ᵥ w))) =
      (∑ i, star (u i) * v i) * (star v ⬝ᵥ w) from by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring]
    rfl
  rw [hdot, norm_mul]
  have h1 := norm_dotProduct_le u v
  have h2 := norm_dotProduct_le v w
  have hvnorm : l2norm v ^ 2 = colNormSq B k := by
    rw [l2norm_sq, colNormSq]
  calc ‖star u ⬝ᵥ v‖ * ‖star v ⬝ᵥ w‖
      ≤ (l2norm u * l2norm v) * (l2norm v * l2norm w) := by
        exact mul_le_mul h1 h2 (norm_nonneg _)
          (mul_nonneg (l2norm_nonneg _) (l2norm_nonneg _))
  _ = colNormSq B k * l2norm u * l2norm w := by
      rw [← hvnorm]
      ring

/-- **Book §5.2.1 analysis display** (C5-09): `𝔼Y = q·BB*` (the book's
`q = p/n`).  Explicit source declaration. -/
theorem expectation_column_gram (B : Matrix m n ℂ) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) {δ : n → Ω → ℝ}
    (hmeas : ∀ k, Measurable (δ k)) (hlaw : ∀ k, IsBernoulli q (δ k) μ) :
    (∑ k, expectation μ (fun ω => δ k ω • colGram B k)) = q • (B * Bᴴ) := by
  have h1 : ∀ k, expectation μ (fun ω => δ k ω • colGram B k) =
      q • colGram B k := by
    intro k
    ext i j
    rw [expectation_apply, Matrix.smul_apply]
    have h2 : (fun ω => (δ k ω • colGram B k) i j) =
        fun ω => δ k ω • colGram B k i j := by
      funext ω
      rw [Matrix.smul_apply]
    rw [h2, integral_smul_const, integral_id_isBernoulli hq (hmeas k) (hlaw k)]
  rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.smul_sum]
  congr 1
  -- `Σ_k B·E_kk·B* = B·B*`
  have h3 : (∑ k, colGram B k) = B * (∑ k : n, Matrix.single k k (1:ℂ)) * Bᴴ := by
    rw [Finset.sum_congr rfl fun k _ => rfl]
    rw [show B * (∑ k : n, Matrix.single k k (1:ℂ)) * Bᴴ =
      ∑ k, B * Matrix.single k k (1 : ℂ) * Bᴴ from by
        rw [Matrix.mul_sum, Matrix.sum_mul]]
    rfl
  rw [h3, sum_single_diag_one, Matrix.mul_one]

/-- Lean implementation helper: `‖Z‖² = λ_max(ZZ*)` — the book's identification
`σ₁(Z)² = λ_max(ZZ*)` in its norm form ((2.1.24)/(2.1.28)). -/
lemma sq_norm_eq_lambdaMax_gram (Z : Matrix m n ℂ) :
    ‖Z‖ ^ 2 = lambdaMax (Matrix.isHermitian_mul_conjTranspose_self Z) := by
  rw [(l2_opNorm_sq_eq Z).1]
  exact posSemidef_l2_opNorm_eq_lambdaMax
    (Matrix.posSemidef_self_mul_conjTranspose Z)

end Model

section MainBounds

variable [Nonempty m] [Nonempty n]

/-- Lean implementation helper: the Chernoff hypotheses for the column-sampling
family. -/
lemma column_family_bounds (B : Matrix m n ℂ) {δ : n → Ω → ℝ}
    (hrange : ∀ k ω, δ k ω = 0 ∨ δ k ω = 1)
    (hherm : ∀ (k : n) ω, ((fun k ω => δ k ω • colGram B k) k ω).IsHermitian) :
    (∀ k ω, 0 ≤ lambdaMin (hherm k ω)) ∧
      (∀ k ω, lambdaMax (hherm k ω) ≤
        Finset.univ.sup' Finset.univ_nonempty (colNormSq B)) := by
  have hpsd : ∀ (k : n) ω, (δ k ω • colGram B k).PosSemidef := by
    intro k ω
    rcases hrange k ω with h | h <;> rw [h]
    · rw [zero_smul]
      exact Matrix.PosSemidef.zero
    · rw [one_smul]
      exact posSemidef_colGram B k
  constructor
  · intro k ω
    exact le_lambdaMin _ fun i => (hpsd k ω).eigenvalues_nonneg i
  · intro k ω
    have h1 : lambdaMax (hherm k ω) ≤ ‖δ k ω • colGram B k‖ :=
      (le_abs_self _).trans (abs_lambdaMax_le _)
    refine h1.trans ?_
    have h2 : ‖δ k ω • colGram B k‖ ≤ ‖colGram B k‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      rcases hrange k ω with h | h <;> rw [h]
      · simp [norm_nonneg]
      · simp
    refine h2.trans ((l2_opNorm_colGram_le B k).trans ?_)
    exact Finset.le_sup' _ (Finset.mem_univ k)

/-- **Book (5.2.1)** (§5.2.1, C5-09), upper half:
`𝔼 σ₁(Z)² ≤ 1.72·q·σ₁(B)² + (log d)·max_k ‖b_{:k}‖²` (the book's `q = p/n`),
with `σ₁(Z)² = λ_max(ZZ*)` and `σ₁(B)² = λ_max(BB*)` per the book's
identification. Explicit source declaration.

**Author note.** This pointwise-support form is retained for compatibility; see
`column_submatrix_upper_of_isBernoulli` for the source-faithful law-only
sibling. -/
theorem column_submatrix_upper (B : Matrix m n ℂ) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) {δ : n → Ω → ℝ}
    (hmeas : ∀ k, Measurable (δ k)) (hlaw : ∀ k, IsBernoulli q (δ k) μ)
    (hrange : ∀ k ω, δ k ω = 0 ∨ δ k ω = 1)
    (hind : ProbabilityTheory.iIndepFun δ μ) :
    ∫ ω, lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (columnSubmatrix B δ ω)) ∂μ ≤
      1.72 * (q * lambdaMax (Matrix.isHermitian_mul_conjTranspose_self B)) +
        Real.log (Fintype.card m) *
          Finset.univ.sup' Finset.univ_nonempty (colNormSq B) := by
  classical
  set X : n → Ω → Matrix m m ℂ := fun k ω => δ k ω • colGram B k with hXdef
  have hherm : ∀ (k : n) ω, (X k ω).IsHermitian := fun k ω =>
    isHermitian_real_smul (posSemidef_colGram B k).1 _
  obtain ⟨hmin, hmax⟩ := column_family_bounds B hrange hherm
  have hXmeas : ∀ k, Measurable (X k) := fun k => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => δ k ω • colGram B k i j
    exact (hmeas k).smul_const _
  have hXind : ProbabilityTheory.iIndepFun X μ := by
    refine hind.comp (fun k s => s • colGram B k) fun k => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun s : ℝ => s • colGram B k i j
    exact measurable_id.smul_const _
  have hLnn : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (colNormSq B) := by
    obtain ⟨k⟩ := (inferInstance : Nonempty n)
    exact (colNormSq_nonneg B k).trans (Finset.le_sup' _ (Finset.mem_univ k))
  have h := matrix_chernoff_expectation_upper_simple (μ := μ) hXmeas hherm
    hmin hmax hLnn hXind
  -- transport the integrand to `λ_max(ZZ*)`
  have hcongr : (fun ω => lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hherm k ω))) = fun ω => lambdaMax
        (Matrix.isHermitian_mul_conjTranspose_self (columnSubmatrix B δ ω)) := by
    funext ω
    exact (lambdaMax_congr (columnSubmatrix_gram B hrange ω).symm _ _)
  rw [hcongr] at h
  refine h.trans ?_
  -- identify `μ_max = q·λ_max(BB*)`
  have hmu : lambdaMax (isHermitian_sum_expectation (μ := μ) hherm) =
      q * lambdaMax (Matrix.isHermitian_mul_conjTranspose_self B) := by
    rw [lambdaMax_congr (expectation_column_gram B hq hmeas hlaw)
      (isHermitian_sum_expectation (μ := μ) hherm)
      (isHermitian_real_smul (Matrix.isHermitian_mul_conjTranspose_self B) q)]
    exact lambdaMax_smul_nonneg (Matrix.isHermitian_mul_conjTranspose_self B)
      hq.1 _
  rw [hmu]
  linarith [Real.log_nonneg (show (1:ℝ) ≤ Fintype.card m by
    exact_mod_cast Fintype.card_pos)]

/-- **Book (5.2.1)** (§5.2.1, C5-09), lower half:
`𝔼 σ_d(Z)² ≥ 0.63·q·σ_d(B)² − (log d)·max_k ‖b_{:k}‖²`, with
`σ_d(Z)² = λ_min(ZZ*)`, `σ_d(B)² = λ_min(BB*)`. Explicit source declaration.

**Author note.** This pointwise-support form is retained for compatibility; see
`column_submatrix_lower_of_isBernoulli` for the source-faithful law-only
sibling. -/
theorem column_submatrix_lower (B : Matrix m n ℂ) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) {δ : n → Ω → ℝ}
    (hmeas : ∀ k, Measurable (δ k)) (hlaw : ∀ k, IsBernoulli q (δ k) μ)
    (hrange : ∀ k ω, δ k ω = 0 ∨ δ k ω = 1)
    (hind : ProbabilityTheory.iIndepFun δ μ) :
    0.63 * (q * lambdaMin (Matrix.isHermitian_mul_conjTranspose_self B)) -
        Real.log (Fintype.card m) *
          Finset.univ.sup' Finset.univ_nonempty (colNormSq B) ≤
      ∫ ω, lambdaMin (Matrix.isHermitian_mul_conjTranspose_self
        (columnSubmatrix B δ ω)) ∂μ := by
  classical
  set X : n → Ω → Matrix m m ℂ := fun k ω => δ k ω • colGram B k with hXdef
  have hherm : ∀ (k : n) ω, (X k ω).IsHermitian := fun k ω =>
    isHermitian_real_smul (posSemidef_colGram B k).1 _
  obtain ⟨hmin, hmax⟩ := column_family_bounds B hrange hherm
  have hXmeas : ∀ k, Measurable (X k) := fun k => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => δ k ω • colGram B k i j
    exact (hmeas k).smul_const _
  have hXind : ProbabilityTheory.iIndepFun X μ := by
    refine hind.comp (fun k s => s • colGram B k) fun k => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun s : ℝ => s • colGram B k i j
    exact measurable_id.smul_const _
  have hLnn : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (colNormSq B) := by
    obtain ⟨k⟩ := (inferInstance : Nonempty n)
    exact (colNormSq_nonneg B k).trans (Finset.le_sup' _ (Finset.mem_univ k))
  have h := matrix_chernoff_expectation_lower_simple (μ := μ) hXmeas hherm
    hmin hmax hLnn hXind
  have hcongr : (fun ω => lambdaMin (isHermitian_matsum Finset.univ
      (fun k => hherm k ω))) = fun ω => lambdaMin
        (Matrix.isHermitian_mul_conjTranspose_self (columnSubmatrix B δ ω)) := by
    funext ω
    exact (lambdaMin_congr (columnSubmatrix_gram B hrange ω).symm _ _)
  rw [hcongr] at h
  refine le_trans ?_ h
  have hmu : lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) =
      q * lambdaMin (Matrix.isHermitian_mul_conjTranspose_self B) := by
    rw [lambdaMin_congr (expectation_column_gram B hq hmeas hlaw)
      (isHermitian_sum_expectation (μ := μ) hherm)
      (isHermitian_real_smul (Matrix.isHermitian_mul_conjTranspose_self B) q)]
    exact lambdaMin_smul_nonneg (Matrix.isHermitian_mul_conjTranspose_self B)
      hq.1 _
  rw [hmu]
  linarith [Real.log_nonneg (show (1:ℝ) ≤ Fintype.card m by
    exact_mod_cast Fintype.card_pos)]

end MainBounds

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# A random row and column submatrix (Tropp §5.2.2)

Formalizes the row-and-column submatrix model and **Book (5.2.2)** (C5-11):

* `projDiag` — the book's random projectors `P = diag(δ₁,…,δ_d)` and
  `R = diag(ξ₁,…,ξ_n)`; `rowSubmatrix` (`PB`) and `rowColumnSubmatrix`
  (`Z = PBR`, realized as a column submatrix of `PB` and reconciled with the
  book's product form by `rowColumnSubmatrix_eq`);
* the two independent Bernoulli families live on separate probability spaces
  `(Ω₁, μ₁)` and `(Ω₂, μ₂)`, and all expectations are stated as iterated
  integrals `𝔼_{ω₁} 𝔼_{ω₂}` — this is exactly the book's conditional form
  `𝔼[𝔼[… | P]]`, and it renders "independent random projectors" precisely;
* `lambdaMax_diagonal_ofReal` — the diagonal-matrix eigenvalue computation
  `λ_max(diag c) = max_k c_k` used throughout the §5.2.2 analysis;
* `conditional_column_bound` — **Book (5.2.3)**, obtained by applying the
  §5.2.1 theorem conditionally on `P`;
* `row_sampling_gram_bound` — **Book (5.2.4)**, via
  `λ_max(CC*) = λ_max(C*C)` (both are `‖C‖²`) and the §5.2.1 theorem for `B*`;
* `max_column_norm_bound` — **Book (5.2.5)**, via the
  book's representation of the maximum column norm as `λ_max` of a sum of
  independent random diagonal matrices;
* `row_column_submatrix_norm` — the main bound **Book (5.2.2)**, combining the three
  displays with the book's constant simplification (`1.72² ≤ 3`, `1.72 ≤ 2`).

The Bernoulli parameters are abstract `p̂ = p/d`, `r̂ = r/n ∈ [0,1]` (the book's
`p` and `r` are the *expected* numbers of rows/columns; the parameters of the
Bernoulli variables are `p/d` and `r/n`, which is what appears in every bound).

-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω₁ : Type*} [MeasurableSpace Ω₁] {μ₁ : MeasureTheory.Measure Ω₁}
variable {Ω₂ : Type*} [MeasurableSpace Ω₂] {μ₂ : MeasureTheory.Measure Ω₂}
variable [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

section DiagonalToolkit

variable {c : n → ℝ}

/-- Lean implementation helper: `‖e_k‖ = 1` for the standard basis vector. -/
lemma l2norm_single (k : n) : l2norm (Pi.single k (1 : ℂ)) = 1 := by
  have h1 : l2norm (Pi.single k (1 : ℂ)) ^ 2 = 1 := by
    rw [l2norm_sq, Finset.sum_eq_single k]
    · simp
    · intro b _ hbk
      rw [Pi.single_eq_of_ne hbk]
      simp
    · intro h
      exact absurd (Finset.mem_univ k) h
  have h2 : (l2norm (Pi.single k (1 : ℂ)) - 1) *
      (l2norm (Pi.single k (1 : ℂ)) + 1) = 0 := by nlinarith [h1]
  rcases mul_eq_zero.mp h2 with h | h
  · linarith
  · linarith [l2norm_nonneg (Pi.single k (1 : ℂ))]

/-- Lean implementation helper: a real diagonal matrix is Hermitian. -/
lemma isHermitian_diagonal_coe (c : n → ℝ) :
    (Matrix.diagonal fun k => ((c k : ℝ) : ℂ)).IsHermitian := by
  show (Matrix.diagonal fun k => ((c k : ℝ) : ℂ))ᴴ =
    Matrix.diagonal fun k => ((c k : ℝ) : ℂ)
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

/-- Lean implementation helper: quadratic form of a real diagonal matrix. -/
lemma rayleigh_diagonal_ofReal (c : n → ℝ) (u : n → ℂ) :
    rayleigh (Matrix.diagonal fun k => ((c k : ℝ) : ℂ)) u =
      ∑ k, c k * ‖u k‖ ^ 2 := by
  have hcomp : star u ⬝ᵥ ((Matrix.diagonal fun k => ((c k : ℝ) : ℂ)) *ᵥ u) =
      ∑ k, star (u k) * (((c k : ℝ) : ℂ) * u k) := by
    rw [show (Matrix.diagonal fun k => ((c k : ℝ) : ℂ)) *ᵥ u =
      fun k => ((c k : ℝ) : ℂ) * u k from funext fun k => by
        rw [Matrix.mulVec_diagonal]]
    rfl
  rw [rayleigh, hcomp, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show star (u k) * (((c k : ℝ) : ℂ) * u k) =
    ((c k : ℝ) : ℂ) * (star (u k) * u k) from by ring]
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  rw [show ((c k : ℝ) : ℂ) * (((‖u k‖ ^ 2 : ℝ)) : ℂ) =
    (((c k * ‖u k‖ ^ 2 : ℝ)) : ℂ) from by push_cast; ring]
  exact Complex.ofReal_re _

/-- **Book §5.2.2 analysis** (C5-11 implicit): the maximum eigenvalue of a real
diagonal matrix is the largest diagonal entry (used for `L`, for `μ_max`, and
for the representation of the maximum column norm).  Implicit source
declaration. -/
lemma lambdaMax_diagonal_ofReal (c : n → ℝ) :
    lambdaMax (isHermitian_diagonal_coe c) =
      Finset.univ.sup' Finset.univ_nonempty c := by
  refine le_antisymm ?_ ?_
  · refine lambdaMax_le_of_forall_rayleigh _ fun u hu => ?_
    rw [rayleigh_diagonal_ofReal]
    calc ∑ k, c k * ‖u k‖ ^ 2
        ≤ ∑ k, Finset.univ.sup' Finset.univ_nonempty c * ‖u k‖ ^ 2 :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
            (Finset.le_sup' c (Finset.mem_univ k)) (by positivity)
      _ = Finset.univ.sup' Finset.univ_nonempty c * l2norm u ^ 2 := by
          rw [← Finset.mul_sum, l2norm_sq]
      _ = _ := by rw [hu]; ring
  · refine Finset.sup'_le _ _ fun k _ => ?_
    have h := rayleigh_le_lambdaMax_of_unit (isHermitian_diagonal_coe c)
      (l2norm_single k)
    rw [rayleigh_diagonal_ofReal, Finset.sum_eq_single k] at h
    · rw [Pi.single_eq_same] at h
      simpa using h
    · intro b _ hbk
      rw [Pi.single_eq_of_ne hbk]
      simp
    · intro h'
      exact absurd (Finset.mem_univ k) h'

/-- Lean implementation helper: a real diagonal matrix with nonnegative
entries is positive semidefinite. -/
lemma posSemidef_diagonal_ofReal (hc : ∀ k, 0 ≤ c k) :
    (Matrix.diagonal fun k => ((c k : ℝ) : ℂ)).PosSemidef := by
  refine posSemidef_iff_isHermitian_quadratic.mpr
    ⟨isHermitian_diagonal_coe c, fun u => ?_⟩
  have h : (star u ⬝ᵥ ((Matrix.diagonal fun k => ((c k : ℝ) : ℂ)) *ᵥ u)).re =
      rayleigh (Matrix.diagonal fun k => ((c k : ℝ) : ℂ)) u := rfl
  rw [h, rayleigh_diagonal_ofReal]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (by positivity)

/-- Lean implementation helper: norm of a psd real diagonal matrix. -/
lemma l2_opNorm_diagonal_ofReal (hc : ∀ k, 0 ≤ c k) :
    ‖Matrix.diagonal fun k => ((c k : ℝ) : ℂ)‖ =
      Finset.univ.sup' Finset.univ_nonempty c := by
  rw [posSemidef_l2_opNorm_eq_lambdaMax (posSemidef_diagonal_ofReal hc)]
  exact lambdaMax_diagonal_ofReal c

end DiagonalToolkit

section Model

/-- **Book §5.2.2** (C5-11): the random projector `P = diag(δ₁,…,δ_d)`
(resp. `R = diag(ξ₁,…,ξ_n)`).  Explicit source declaration. -/
noncomputable def projDiag {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (δ : ι → Ω → ℝ) (ω : Ω) : Matrix ι ι ℂ :=
  Matrix.diagonal fun j => ((δ j ω : ℝ) : ℂ)

/-- **Book §5.2.2** (C5-11): the row submatrix `PB`.  Explicit source
declaration (an intermediate object of the analysis). -/
noncomputable def rowSubmatrix (B : Matrix d n ℂ) (δ : d → Ω₁ → ℝ)
    (ω₁ : Ω₁) : Matrix d n ℂ :=
  projDiag δ ω₁ * B

/-- **Book §5.2.2** (C5-11): the random row-and-column submatrix `Z = PBR`,
realized as the §5.2.1 column submatrix of `PB` (see
`rowColumnSubmatrix_eq` for the book's product form).  Explicit source
declaration. -/
noncomputable def rowColumnSubmatrix (B : Matrix d n ℂ) (δ : d → Ω₁ → ℝ)
    (ξ : n → Ω₂ → ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) : Matrix d n ℂ :=
  columnSubmatrix (rowSubmatrix B δ ω₁) ξ ω₂

/-- Lean implementation helper: rectangular version of the real/complex
scalar-action bridge. -/
lemma real_smul_eq_complex_smul_rect (r : ℝ) (A : Matrix d n ℂ) :
    r • A = (r : ℂ) • A := by
  ext i j
  rw [Matrix.smul_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- Lean implementation helper: a §5.2.1 column submatrix is right
multiplication by the diagonal projector. -/
lemma columnSubmatrix_eq_mul_projDiag (B' : Matrix d n ℂ) (ξ : n → Ω₂ → ℝ)
    (ω₂ : Ω₂) : columnSubmatrix B' ξ ω₂ = B' * projDiag ξ ω₂ := by
  have hdiag : projDiag ξ ω₂ =
      ∑ k, ((ξ k ω₂ : ℝ) : ℂ) • Matrix.single k k (1 : ℂ) := by
    ext i j
    rw [projDiag, Matrix.diagonal_apply]
    rw [show (∑ k, ((ξ k ω₂ : ℝ) : ℂ) • Matrix.single k k (1 : ℂ)) i j =
      ∑ k, ((ξ k ω₂ : ℝ) : ℂ) * Matrix.single k k (1 : ℂ) i j from by
        rw [Matrix.sum_apply]
        exact Finset.sum_congr rfl fun k _ => rfl]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, Finset.sum_eq_single i]
      · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, mul_one]
      · intro b _ hbi
        rw [Matrix.single_apply, if_neg (fun h => hbi h.1), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    · rw [if_neg hij]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      rw [Matrix.single_apply, if_neg (fun h => hij (h.1.symm.trans h.2)),
        mul_zero]
  rw [columnSubmatrix, hdiag, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul]
  exact real_smul_eq_complex_smul_rect (ξ k ω₂) (B' * Matrix.single k k (1 : ℂ))

/-- **Book §5.2.2** (C5-11): `Z = PBR`, the book's displayed product form.
Explicit source declaration. -/
lemma rowColumnSubmatrix_eq (B : Matrix d n ℂ) (δ : d → Ω₁ → ℝ)
    (ξ : n → Ω₂ → ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) :
    rowColumnSubmatrix B δ ξ ω₁ ω₂ =
      projDiag δ ω₁ * B * projDiag ξ ω₂ := by
  rw [rowColumnSubmatrix, columnSubmatrix_eq_mul_projDiag, rowSubmatrix]

/-- Lean implementation helper: `(PB)* = B*P`, so the row submatrix is the
conjugate transpose of a column submatrix of `B*`. -/
lemma rowSubmatrix_eq_conjTranspose (B : Matrix d n ℂ) (δ : d → Ω₁ → ℝ)
    (ω₁ : Ω₁) :
    rowSubmatrix B δ ω₁ = (columnSubmatrix Bᴴ δ ω₁)ᴴ := by
  rw [columnSubmatrix_eq_mul_projDiag, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, rowSubmatrix]
  congr 1
  rw [projDiag, Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

/-- Lean implementation helper: entries of the row submatrix. -/
lemma rowSubmatrix_apply (B : Matrix d n ℂ) (δ : d → Ω₁ → ℝ) (ω₁ : Ω₁)
    (j : d) (k : n) :
    rowSubmatrix B δ ω₁ j k = ((δ j ω₁ : ℝ) : ℂ) * B j k := by
  rw [rowSubmatrix, projDiag, Matrix.diagonal_mul]

/-- Lean implementation helper: `‖P‖ ≤ 1` for a 0/1 diagonal projector. -/
lemma l2_opNorm_projDiag_le_one {δ : d → Ω₁ → ℝ}
    (hrange : ∀ j ω, δ j ω = 0 ∨ δ j ω = 1) (ω₁ : Ω₁) :
    ‖projDiag δ ω₁‖ ≤ 1 := by
  have h0 : ∀ j, 0 ≤ δ j ω₁ := fun j => by
    rcases hrange j ω₁ with h | h <;> simp [h]
  rw [projDiag, l2_opNorm_diagonal_ofReal h0]
  refine Finset.sup'_le _ _ fun j _ => ?_
  rcases hrange j ω₁ with h | h <;> simp [h]

/-- Lean implementation helper: `‖PB‖ ≤ ‖B‖`. -/
lemma l2_opNorm_rowSubmatrix_le (B : Matrix d n ℂ) {δ : d → Ω₁ → ℝ}
    (hrange : ∀ j ω, δ j ω = 0 ∨ δ j ω = 1) (ω₁ : Ω₁) :
    ‖rowSubmatrix B δ ω₁‖ ≤ ‖B‖ := by
  rw [rowSubmatrix]
  calc ‖projDiag δ ω₁ * B‖ ≤ ‖projDiag δ ω₁‖ * ‖B‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * ‖B‖ := mul_le_mul_of_nonneg_right
        (l2_opNorm_projDiag_le_one hrange ω₁) (norm_nonneg B)
    _ = ‖B‖ := one_mul _

/-- Lean implementation helper: column norms only shrink under row sampling. -/
lemma colNormSq_rowSubmatrix_le (B : Matrix d n ℂ) {δ : d → Ω₁ → ℝ}
    (hrange : ∀ j ω, δ j ω = 0 ∨ δ j ω = 1) (ω₁ : Ω₁) (k : n) :
    colNormSq (rowSubmatrix B δ ω₁) k ≤ colNormSq B k := by
  rw [colNormSq, colNormSq]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [rowSubmatrix_apply, norm_mul]
  rcases hrange j ω₁ with h | h <;> rw [h]
  · simp
  · simp

/-- **Book §5.2.2 analysis** (C5-11 implicit): the squared column norms of
`PB` — "`‖(PB)_{:k}‖² = Σ_j δ_j |b_jk|²`" (uses `δ² = δ`).  Explicit source
display. -/
lemma colNormSq_rowSubmatrix (B : Matrix d n ℂ) {δ : d → Ω₁ → ℝ}
    (hrange : ∀ j ω, δ j ω = 0 ∨ δ j ω = 1) (ω₁ : Ω₁) (k : n) :
    colNormSq (rowSubmatrix B δ ω₁) k = ∑ j, δ j ω₁ * ‖B j k‖ ^ 2 := by
  rw [colNormSq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rowSubmatrix_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  rcases hrange j ω₁ with h | h <;> rw [h] <;> ring

/-- Lean implementation helper: measurability of the row submatrix. -/
lemma measurable_rowSubmatrix (B : Matrix d n ℂ) {δ : d → Ω₁ → ℝ}
    (hmeas : ∀ j, Measurable (δ j)) :
    Measurable fun ω₁ => rowSubmatrix B δ ω₁ := by
  apply measurable_pi_lambda
  intro j
  apply measurable_pi_lambda
  intro k
  have h : (fun ω₁ => rowSubmatrix B δ ω₁ j k) =
      fun ω₁ => ((δ j ω₁ : ℝ) : ℂ) * B j k :=
    funext fun ω₁ => rowSubmatrix_apply B δ ω₁ j k
  rw [h]
  exact (Complex.measurable_ofReal.comp (hmeas j)).mul_const _

end Model

section GramFacts

variable {B : Matrix d n ℂ} {δ : d → Ω₁ → ℝ} {ξ : n → Ω₂ → ℝ}

/-- Lean implementation helper: the gram norm bound
`λ_max((PB)(PB)*) = ‖PB‖² ≤ ‖B‖²` and its measurability, packaged as
integrability of `ω₁ ↦ λ_max((PB)(PB)*)`. -/
lemma integrable_lambdaMax_gram_rowSubmatrix
    (hmeas : ∀ j, Measurable (δ j))
    (hrange : ∀ j ω, δ j ω = 0 ∨ δ j ω = 1) :
    Integrable (fun ω₁ => lambdaMax
      (Matrix.isHermitian_mul_conjTranspose_self (rowSubmatrix B δ ω₁)))
      μ₁ := by
  have hgmeas : Measurable fun ω₁ =>
      rowSubmatrix B δ ω₁ * (rowSubmatrix B δ ω₁)ᴴ := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    have h : (fun ω₁ => (rowSubmatrix B δ ω₁ * (rowSubmatrix B δ ω₁)ᴴ) i j) =
        fun ω₁ => ∑ k, rowSubmatrix B δ ω₁ i k *
          star (rowSubmatrix B δ ω₁ j k) := by
      funext ω₁
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Matrix.conjTranspose_apply]
    rw [h]
    refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
    · exact (measurable_entry i k).comp (measurable_rowSubmatrix B hmeas)
    · exact continuous_star.measurable.comp ((measurable_entry j k).comp
        (measurable_rowSubmatrix B hmeas))
  have hbd : ∀ ω₁, ‖rowSubmatrix B δ ω₁ * (rowSubmatrix B δ ω₁)ᴴ‖ ≤
      ‖B‖ ^ 2 := fun ω₁ => by
    calc ‖rowSubmatrix B δ ω₁ * (rowSubmatrix B δ ω₁)ᴴ‖
        ≤ ‖rowSubmatrix B δ ω₁‖ * ‖(rowSubmatrix B δ ω₁)ᴴ‖ :=
          Matrix.l2_opNorm_mul _ _
      _ = ‖rowSubmatrix B δ ω₁‖ * ‖rowSubmatrix B δ ω₁‖ := by
          rw [Matrix.l2_opNorm_conjTranspose]
      _ ≤ ‖B‖ * ‖B‖ := mul_le_mul (l2_opNorm_rowSubmatrix_le B hrange ω₁)
          (l2_opNorm_rowSubmatrix_le B hrange ω₁) (norm_nonneg _)
          (norm_nonneg _)
      _ = ‖B‖ ^ 2 := (sq ‖B‖).symm
  exact integrable_lambdaMax hgmeas
    (fun ω₁ => Matrix.isHermitian_mul_conjTranspose_self _) hbd

/-- Lean implementation helper: integrability of the maximum column norm of
`PB`. -/
lemma integrable_sup_colNormSq_rowSubmatrix
    (hmeas : ∀ j, Measurable (δ j))
    (hrange : ∀ j ω, δ j ω = 0 ∨ δ j ω = 1) :
    Integrable (fun ω₁ => Finset.univ.sup' Finset.univ_nonempty
      (colNormSq (rowSubmatrix B δ ω₁))) μ₁ := by
  refine Integrable.of_bound ?_
    (Finset.univ.sup' Finset.univ_nonempty (colNormSq B)) ?_
  · have hm := Finset.measurable_sup' (s := (Finset.univ : Finset n))
      Finset.univ_nonempty
      (f := fun k (ω₁ : Ω₁) => colNormSq (rowSubmatrix B δ ω₁) k)
      (fun k _ => ?_)
    · have heq : (Finset.univ.sup' Finset.univ_nonempty
          (fun k (ω₁ : Ω₁) => colNormSq (rowSubmatrix B δ ω₁) k)) =
          fun ω₁ => Finset.univ.sup' Finset.univ_nonempty
            (colNormSq (rowSubmatrix B δ ω₁)) := by
        funext ω₁
        exact Finset.sup'_apply _ _ _
      rw [heq] at hm
      exact hm.aestronglyMeasurable
    · have h : (fun ω₁ => colNormSq (rowSubmatrix B δ ω₁) k) =
          fun ω₁ => ∑ j, δ j ω₁ * ‖B j k‖ ^ 2 :=
        funext fun ω₁ => colNormSq_rowSubmatrix B hrange ω₁ k
      rw [h]
      exact Finset.measurable_sum _ fun j _ => (hmeas j).mul_const _
  · refine Filter.Eventually.of_forall fun ω₁ => ?_
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · refine le_trans ?_ (Finset.le_sup'
        (colNormSq (rowSubmatrix B δ ω₁)) (Finset.mem_univ Classical.ofNonempty))
      have h := colNormSq_nonneg (rowSubmatrix B δ ω₁)
        (Classical.ofNonempty : n)
      have h0 : (0 : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty
          (colNormSq B) :=
        (colNormSq_nonneg B (Classical.ofNonempty : n)).trans
          (Finset.le_sup' _ (Finset.mem_univ _))
      linarith
    · refine Finset.sup'_le _ _ fun k _ => ?_
      exact (colNormSq_rowSubmatrix_le B hrange ω₁ k).trans
        (Finset.le_sup' (colNormSq B) (Finset.mem_univ k))

end GramFacts

section ConditionalBound

variable {B : Matrix d n ℂ} {δ : d → Ω₁ → ℝ} {ξ : n → Ω₂ → ℝ}

/-- Lean implementation helper: the §5.2.1 bound applied conditionally on
`P` (the book: "Invoking the matrix Chernoff inequality **(5.1.8)**,
conditional on the choice of `P`").

**Author note.** This pointwise-support helper is retained for compatibility;
see `conditional_column_bound_pointwise_of_isBernoulli` for the law-only
counterpart. -/
lemma conditional_column_bound_pointwise {rq : ℝ}
    (hrq : rq ∈ Set.Icc (0 : ℝ) 1)
    (hξmeas : ∀ k, Measurable (ξ k)) (hξlaw : ∀ k, IsBernoulli rq (ξ k) μ₂)
    (hξrange : ∀ k ω, ξ k ω = 0 ∨ ξ k ω = 1)
    (hξind : ProbabilityTheory.iIndepFun ξ μ₂) (ω₁ : Ω₁) :
    ∫ ω₂, lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (rowColumnSubmatrix B δ ξ ω₁ ω₂)) ∂μ₂ ≤
      1.72 * (rq * lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
          (rowSubmatrix B δ ω₁))) +
        Real.log (Fintype.card d) * Finset.univ.sup' Finset.univ_nonempty
          (colNormSq (rowSubmatrix B δ ω₁)) :=
  column_submatrix_upper (μ := μ₂) (rowSubmatrix B δ ω₁) hrq hξmeas hξlaw
    hξrange hξind

/-- **Book (5.2.3)** (C5-11):
`𝔼‖Z‖² ≤ 1.72·r̂·𝔼λ_max((PB)(PB)*) + (log d)·𝔼 max_k ‖(PB)_{:k}‖²`.
The expectation is expressed by conditioning on `P`.

**Author note.** This pointwise-support form is retained for compatibility; see
`conditional_column_bound_of_isBernoulli` for the source-faithful law-only
sibling. -/
theorem conditional_column_bound {rq : ℝ}
    (hrq : rq ∈ Set.Icc (0 : ℝ) 1)
    (hδmeas : ∀ j, Measurable (δ j))
    (hδrange : ∀ j ω, δ j ω = 0 ∨ δ j ω = 1)
    (hξmeas : ∀ k, Measurable (ξ k)) (hξlaw : ∀ k, IsBernoulli rq (ξ k) μ₂)
    (hξrange : ∀ k ω, ξ k ω = 0 ∨ ξ k ω = 1)
    (hξind : ProbabilityTheory.iIndepFun ξ μ₂) :
    ∫ ω₁, (∫ ω₂, ‖rowColumnSubmatrix B δ ξ ω₁ ω₂‖ ^ 2 ∂μ₂) ∂μ₁ ≤
      1.72 * (rq * ∫ ω₁, lambdaMax
          (Matrix.isHermitian_mul_conjTranspose_self
            (rowSubmatrix B δ ω₁)) ∂μ₁) +
        Real.log (Fintype.card d) *
          ∫ ω₁, Finset.univ.sup' Finset.univ_nonempty
            (colNormSq (rowSubmatrix B δ ω₁)) ∂μ₁ := by
  have hlogd : 0 ≤ Real.log (Fintype.card d) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hnormeq : ∀ ω₁ ω₂, ‖rowColumnSubmatrix B δ ξ ω₁ ω₂‖ ^ 2 =
      lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (rowColumnSubmatrix B δ ξ ω₁ ω₂)) :=
    fun ω₁ ω₂ => sq_norm_eq_lambdaMax_gram _
  -- pointwise bound on the inner expectation
  have hpt : ∀ ω₁, ∫ ω₂, ‖rowColumnSubmatrix B δ ξ ω₁ ω₂‖ ^ 2 ∂μ₂ ≤
      1.72 * (rq * lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
          (rowSubmatrix B δ ω₁))) +
        Real.log (Fintype.card d) * Finset.univ.sup' Finset.univ_nonempty
          (colNormSq (rowSubmatrix B δ ω₁)) := fun ω₁ => by
    rw [show (fun ω₂ => ‖rowColumnSubmatrix B δ ξ ω₁ ω₂‖ ^ 2) =
      fun ω₂ => lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (rowColumnSubmatrix B δ ξ ω₁ ω₂)) from funext fun ω₂ => hnormeq ω₁ ω₂]
    exact conditional_column_bound_pointwise hrq hξmeas hξlaw hξrange hξind ω₁
  -- integrate the pointwise bound
  have hg1 := integrable_lambdaMax_gram_rowSubmatrix (μ₁ := μ₁) (B := B)
    hδmeas hδrange
  have hg2 := integrable_sup_colNormSq_rowSubmatrix (μ₁ := μ₁) (B := B)
    hδmeas hδrange
  have hgint : Integrable (fun ω₁ =>
      1.72 * (rq * lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
          (rowSubmatrix B δ ω₁))) +
        Real.log (Fintype.card d) * Finset.univ.sup' Finset.univ_nonempty
          (colNormSq (rowSubmatrix B δ ω₁))) μ₁ := by
    refine Integrable.add ?_ ?_
    · exact ((hg1.const_mul rq).const_mul 1.72)
    · exact hg2.const_mul _
  have hmono := integral_mono_of_nonneg (μ := μ₁)
    (f := fun ω₁ => ∫ ω₂, ‖rowColumnSubmatrix B δ ξ ω₁ ω₂‖ ^ 2 ∂μ₂)
    (g := fun ω₁ =>
      1.72 * (rq * lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
          (rowSubmatrix B δ ω₁))) +
        Real.log (Fintype.card d) * Finset.univ.sup' Finset.univ_nonempty
          (colNormSq (rowSubmatrix B δ ω₁)))
    (Filter.Eventually.of_forall fun ω₁ =>
      integral_nonneg fun ω₂ => sq_nonneg _)
    hgint (Filter.Eventually.of_forall hpt)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add ((hg1.const_mul rq).const_mul 1.72) (hg2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]

end ConditionalBound

section RowSamplingBound

variable {B : Matrix d n ℂ} {δ : d → Ω₁ → ℝ}

/-- Lean implementation helper: row norms of `B` as column norms of `B*`. -/
lemma colNormSq_conjTranspose (B : Matrix d n ℂ) (j : d) :
    colNormSq Bᴴ j = ∑ k, ‖B j k‖ ^ 2 := by
  rw [colNormSq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, norm_star]

/-- Lean implementation helper: `λ_max(CC*) = λ_max(C*C)` — the book's
"first identity holds because `λ_max(CC*) = λ_max(C*C)` for any matrix `C`"
(both sides equal `‖C‖²`).  Implicit source declaration. -/
lemma lambdaMax_gram_conjTranspose (C : Matrix d n ℂ) :
    lambdaMax (Matrix.isHermitian_mul_conjTranspose_self C) =
      lambdaMax (Matrix.isHermitian_mul_conjTranspose_self Cᴴ) := by
  rw [← sq_norm_eq_lambdaMax_gram, ← sq_norm_eq_lambdaMax_gram,
    Matrix.l2_opNorm_conjTranspose]

/-- **Book (5.2.4)** (C5-11):
`𝔼λ_max((PB)(PB)*) ≤ 1.72·p̂·‖B‖² + (log n)·max_j ‖b_{j:}‖²` (the book
simplifies `λ_max(B*B) = ‖B‖²`).

**Author note.** This pointwise-support form is retained for compatibility; see
`row_sampling_gram_bound_of_isBernoulli` for the source-faithful law-only
sibling. -/
theorem row_sampling_gram_bound {pq : ℝ}
    (hpq : pq ∈ Set.Icc (0 : ℝ) 1)
    (hδmeas : ∀ j, Measurable (δ j)) (hδlaw : ∀ j, IsBernoulli pq (δ j) μ₁)
    (hδrange : ∀ j ω, δ j ω = 0 ∨ δ j ω = 1)
    (hδind : ProbabilityTheory.iIndepFun δ μ₁) :
    ∫ ω₁, lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (rowSubmatrix B δ ω₁)) ∂μ₁ ≤
      1.72 * (pq * ‖B‖ ^ 2) +
        Real.log (Fintype.card n) * Finset.univ.sup' Finset.univ_nonempty
          (fun j => ∑ k, ‖B j k‖ ^ 2) := by
  -- `λ_max((PB)(PB)*) = λ_max((B*P)(B*P)*)`, pointwise
  have hpt : ∀ ω₁, lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
      (rowSubmatrix B δ ω₁)) =
      lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (columnSubmatrix Bᴴ δ ω₁)) := fun ω₁ => by
    rw [lambdaMax_gram_conjTranspose (rowSubmatrix B δ ω₁)]
    exact lambdaMax_congr
      (by rw [rowSubmatrix_eq_conjTranspose B δ ω₁,
        Matrix.conjTranspose_conjTranspose]) _ _
  rw [show (fun ω₁ => lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
      (rowSubmatrix B δ ω₁))) =
      fun ω₁ => lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (columnSubmatrix Bᴴ δ ω₁)) from funext hpt]
  have h := column_submatrix_upper (μ := μ₁) Bᴴ hpq hδmeas hδlaw hδrange hδind
  refine h.trans (le_of_eq ?_)
  congr 1
  · -- `λ_max(B*(B*)*) = ‖B‖²`
    rw [← sq_norm_eq_lambdaMax_gram, Matrix.l2_opNorm_conjTranspose]
  · congr 1
    refine Finset.sup'_congr _ rfl fun j _ => colNormSq_conjTranspose B j

end RowSamplingBound

section MaxColumnNormBound

variable {B : Matrix d n ℂ} {δ : d → Ω₁ → ℝ}

/-- **Book §5.2.2 analysis** (C5-11): the diagonal coefficient matrices
`diag(|b_{j1}|², …, |b_{jn}|²)` of the max-column-norm representation.
Explicit source display. -/
noncomputable def entryDiag (B : Matrix d n ℂ) (j : d) : Matrix n n ℂ :=
  Matrix.diagonal fun k => ((‖B j k‖ ^ 2 : ℝ) : ℂ)

/-- **Book §5.2.2 analysis** (C5-11): "the maximum column norm [is] the
maximum eigenvalue of a sum of independent, random diagonal matrices":
`max_k ‖(PB)_{:k}‖² = λ_max(Σ_j δ_j · diag(|b_{j1}|²,…,|b_{jn}|²))`.
Explicit source display. -/
lemma sup_colNormSq_eq_lambdaMax
    (hrange : ∀ j ω, δ j ω = 0 ∨ δ j ω = 1) (ω₁ : Ω₁)
    (hherm : (∑ j, δ j ω₁ • entryDiag B j).IsHermitian) :
    Finset.univ.sup' Finset.univ_nonempty
      (colNormSq (rowSubmatrix B δ ω₁)) = lambdaMax hherm := by
  have hsum : (∑ j, δ j ω₁ • entryDiag B j) =
      Matrix.diagonal fun k => (((∑ j, δ j ω₁ * ‖B j k‖ ^ 2 : ℝ)) : ℂ) := by
    ext i k
    rw [Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl]
      rw [show ((((∑ j, δ j ω₁ * ‖B j i‖ ^ 2 : ℝ))) : ℂ) =
        ∑ j, (((δ j ω₁ * ‖B j i‖ ^ 2 : ℝ)) : ℂ) from by push_cast; rfl]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, entryDiag, Matrix.diagonal_apply, if_pos rfl]
      rw [show (δ j ω₁ • ((((‖B j i‖ ^ 2 : ℝ))) : ℂ)) =
        (((δ j ω₁ : ℝ)) : ℂ) * (((‖B j i‖ ^ 2 : ℝ)) : ℂ) from by
          rw [Complex.real_smul]]
      push_cast
      ring
    · rw [if_neg hik]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Matrix.smul_apply, entryDiag, Matrix.diagonal_apply, if_neg hik,
        smul_zero]
  have hlam := lambdaMax_congr hsum hherm
    (isHermitian_diagonal_coe fun k => ∑ j, δ j ω₁ * ‖B j k‖ ^ 2)
  rw [hlam, lambdaMax_diagonal_ofReal]
  refine Finset.sup'_congr _ rfl fun k _ => ?_
  exact colNormSq_rowSubmatrix B hrange ω₁ k

/-- Lean implementation helper: the diagonal summands are Hermitian. -/
lemma isHermitian_smul_entryDiag (j : d) (c : ℝ) :
    (c • entryDiag B j).IsHermitian :=
  isHermitian_real_smul (isHermitian_diagonal_coe _) _

/-- **Book §5.2.2 analysis** (C5-11): the Chernoff parameters of the diagonal
family — `L = max_j max_k |b_jk|²` and the summand eigenvalue bounds.
Explicit source displays. -/
lemma entryDiag_family_bounds
    (hrange : ∀ j ω, δ j ω = 0 ∨ δ j ω = 1)
    (hherm : ∀ (j : d) ω₁,
      ((fun j (ω₁ : Ω₁) => δ j ω₁ • entryDiag B j) j ω₁).IsHermitian) :
    (∀ j ω₁, 0 ≤ lambdaMin (hherm j ω₁)) ∧
      (∀ j ω₁, lambdaMax (hherm j ω₁) ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun j => Finset.univ.sup' Finset.univ_nonempty
            (fun k => ‖B j k‖ ^ 2))) := by
  have hpsd : ∀ (j : d) ω₁, (δ j ω₁ • entryDiag B j).PosSemidef := by
    intro j ω₁
    rcases hrange j ω₁ with h | h <;> rw [h]
    · rw [zero_smul]
      exact Matrix.PosSemidef.zero
    · rw [one_smul]
      exact posSemidef_diagonal_ofReal fun k => by positivity
  constructor
  · intro j ω₁
    exact le_lambdaMin _ fun i => (hpsd j ω₁).eigenvalues_nonneg i
  · intro j ω₁
    have h1 : lambdaMax (hherm j ω₁) ≤ ‖δ j ω₁ • entryDiag B j‖ :=
      (le_abs_self _).trans (abs_lambdaMax_le _)
    refine h1.trans ?_
    have h2 : ‖δ j ω₁ • entryDiag B j‖ ≤ ‖entryDiag B j‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      rcases hrange j ω₁ with h | h <;> rw [h]
      · simp [norm_nonneg]
      · simp
    refine h2.trans ?_
    rw [entryDiag, l2_opNorm_diagonal_ofReal fun k => by positivity]
    exact Finset.le_sup' (f := fun j => Finset.univ.sup' Finset.univ_nonempty
      (fun k => ‖B j k‖ ^ 2)) (Finset.mem_univ j)

/-- **Book §5.2.2 analysis** (C5-11): `μ_max = p̂ · max_k ‖b_{:k}‖²` — the
expectation of the diagonal family is `p̂ · diag(‖b_{:1}‖²,…,‖b_{:n}‖²)`.
Explicit source displays. -/
lemma entryDiag_sum_expectation {pq : ℝ}
    (hpq : pq ∈ Set.Icc (0 : ℝ) 1)
    (hδmeas : ∀ j, Measurable (δ j)) (hδlaw : ∀ j, IsBernoulli pq (δ j) μ₁)
    (hherm : ∀ (j : d) ω₁,
      ((fun j (ω₁ : Ω₁) => δ j ω₁ • entryDiag B j) j ω₁).IsHermitian) :
    lambdaMax (isHermitian_sum_expectation (μ := μ₁) hherm) =
      pq * Finset.univ.sup' Finset.univ_nonempty (colNormSq B) := by
  have h1 : ∀ j : d, expectation μ₁ (fun ω₁ => δ j ω₁ • entryDiag B j) =
      pq • entryDiag B j := by
    intro j
    ext i k
    rw [expectation_apply, Matrix.smul_apply]
    have h2 : (fun ω₁ => (δ j ω₁ • entryDiag B j) i k) =
        fun ω₁ => δ j ω₁ • entryDiag B j i k := by
      funext ω₁
      rw [Matrix.smul_apply]
    rw [h2, integral_smul_const, integral_id_isBernoulli hpq (hδmeas j)
      (hδlaw j)]
  have h3 : (∑ j, expectation μ₁ (fun ω₁ => δ j ω₁ • entryDiag B j)) =
      pq • Matrix.diagonal fun k => ((colNormSq B k : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun j _ => h1 j, ← Finset.smul_sum]
    congr 1
    ext i k
    rw [Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, colNormSq]
      rw [show (((∑ j, ‖B j i‖ ^ 2 : ℝ)) : ℂ) =
        ∑ j, (((‖B j i‖ ^ 2 : ℝ)) : ℂ) from by push_cast; rfl]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [entryDiag, Matrix.diagonal_apply, if_pos rfl]
    · rw [if_neg hik]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [entryDiag, Matrix.diagonal_apply, if_neg hik]
  refine (lambdaMax_congr h3 (isHermitian_sum_expectation (μ := μ₁) hherm)
    (isHermitian_real_smul (isHermitian_diagonal_coe _) _)).trans ?_
  rw [lambdaMax_smul_nonneg (isHermitian_diagonal_coe _) hpq.1
      (isHermitian_real_smul (isHermitian_diagonal_coe _) _),
    lambdaMax_diagonal_ofReal]

/-- **Book (5.2.5)** (C5-11):
`𝔼 max_k ‖(PB)_{:k}‖² ≤ 1.72·p̂·max_k ‖b_{:k}‖² + (log n)·max_{j,k} |b_jk|²`.

**Author note.** This pointwise-support form is retained for compatibility; see
`max_column_norm_bound_of_isBernoulli` for the source-faithful law-only
sibling. -/
theorem max_column_norm_bound {pq : ℝ}
    (hpq : pq ∈ Set.Icc (0 : ℝ) 1)
    (hδmeas : ∀ j, Measurable (δ j)) (hδlaw : ∀ j, IsBernoulli pq (δ j) μ₁)
    (hδrange : ∀ j ω, δ j ω = 0 ∨ δ j ω = 1)
    (hδind : ProbabilityTheory.iIndepFun δ μ₁) :
    ∫ ω₁, Finset.univ.sup' Finset.univ_nonempty
        (colNormSq (rowSubmatrix B δ ω₁)) ∂μ₁ ≤
      1.72 * (pq * Finset.univ.sup' Finset.univ_nonempty (colNormSq B)) +
        Real.log (Fintype.card n) * Finset.univ.sup' Finset.univ_nonempty
          (fun j => Finset.univ.sup' Finset.univ_nonempty
            (fun k => ‖B j k‖ ^ 2)) := by
  classical
  have hherm : ∀ (j : d) ω₁,
      ((fun j (ω₁ : Ω₁) => δ j ω₁ • entryDiag B j) j ω₁).IsHermitian :=
    fun j ω₁ => isHermitian_smul_entryDiag j _
  obtain ⟨hmin, hmax⟩ := entryDiag_family_bounds hδrange hherm
  have hXmeas : ∀ j, Measurable
      ((fun j (ω₁ : Ω₁) => δ j ω₁ • entryDiag B j) j) := fun j => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro k
    show Measurable fun ω₁ => δ j ω₁ • entryDiag B j i k
    exact (hδmeas j).smul_const _
  have hXind : ProbabilityTheory.iIndepFun
      (fun j (ω₁ : Ω₁) => δ j ω₁ • entryDiag B j) μ₁ := by
    refine hδind.comp (fun j s => s • entryDiag B j) fun j => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro k
    show Measurable fun s : ℝ => s • entryDiag B j i k
    exact measurable_id.smul_const _
  have hL0 : (0 : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun j => Finset.univ.sup' Finset.univ_nonempty
        (fun k => ‖B j k‖ ^ 2)) := by
    have h1 : (0 : ℝ) ≤ ‖B (Classical.ofNonempty : d)
        (Classical.ofNonempty : n)‖ ^ 2 := by positivity
    have h2 : ‖B (Classical.ofNonempty : d) (Classical.ofNonempty : n)‖ ^ 2 ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun k => ‖B (Classical.ofNonempty : d) k‖ ^ 2) :=
      Finset.le_sup' (f := fun k => ‖B (Classical.ofNonempty : d) k‖ ^ 2)
        (Finset.mem_univ (Classical.ofNonempty : n))
    have h3 : Finset.univ.sup' Finset.univ_nonempty
        (fun k => ‖B (Classical.ofNonempty : d) k‖ ^ 2) ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun j => Finset.univ.sup' Finset.univ_nonempty
            (fun k => ‖B j k‖ ^ 2)) :=
      Finset.le_sup' (f := fun j => Finset.univ.sup' Finset.univ_nonempty
        (fun k => ‖B j k‖ ^ 2)) (Finset.mem_univ _)
    linarith
  have h := matrix_chernoff_expectation_upper_simple (μ := μ₁) hXmeas hherm
    hmin hmax hL0 hXind
  rw [show (fun ω₁ => Finset.univ.sup' Finset.univ_nonempty
      (colNormSq (rowSubmatrix B δ ω₁))) =
      fun ω₁ => lambdaMax (isHermitian_matsum Finset.univ
        (fun j => hherm j ω₁)) from
    funext fun ω₁ => sup_colNormSq_eq_lambdaMax hδrange ω₁ _]
  rw [entryDiag_sum_expectation hpq hδmeas hδlaw hherm] at h
  refine h.trans (le_of_eq ?_)
  ring

end MaxColumnNormBound

section MainBound

variable {B : Matrix d n ℂ} {δ : d → Ω₁ → ℝ} {ξ : n → Ω₂ → ℝ}

/-- **Book (5.2.2)** (C5-11), the main
result of §5.2.2:

`𝔼‖Z‖² ≤ 3·p̂·r̂·‖B‖² + 2·p̂(log d)·max_k ‖b_{:k}‖²
        + 2·r̂(log n)·max_j ‖b_{j:}‖² + (log d)(log n)·max_{j,k} |b_jk|²`

with `p̂ = p/d`, `r̂ = r/n` the Bernoulli parameters ("We have simplified
numerical constants to make the expression more compact": `1.72² ≤ 3`,
`1.72 ≤ 2`). The expectation is the iterated one, i.e. the book's
`𝔼 = 𝔼_P 𝔼_R [· | P]`.

**Author note.** Lean states the result for abstract Bernoulli parameters
`p̂, r̂ ∈ [0,1]`; the Book specializes them to expected row and column counts.
See `row_column_submatrix_norm_of_isBernoulli` for the law-only sibling. -/
theorem row_column_submatrix_norm {pq rq : ℝ}
    (hpq : pq ∈ Set.Icc (0 : ℝ) 1) (hrq : rq ∈ Set.Icc (0 : ℝ) 1)
    (hδmeas : ∀ j, Measurable (δ j)) (hδlaw : ∀ j, IsBernoulli pq (δ j) μ₁)
    (hδrange : ∀ j ω, δ j ω = 0 ∨ δ j ω = 1)
    (hδind : ProbabilityTheory.iIndepFun δ μ₁)
    (hξmeas : ∀ k, Measurable (ξ k)) (hξlaw : ∀ k, IsBernoulli rq (ξ k) μ₂)
    (hξrange : ∀ k ω, ξ k ω = 0 ∨ ξ k ω = 1)
    (hξind : ProbabilityTheory.iIndepFun ξ μ₂) :
    ∫ ω₁, (∫ ω₂, ‖rowColumnSubmatrix B δ ξ ω₁ ω₂‖ ^ 2 ∂μ₂) ∂μ₁ ≤
      3 * (pq * rq * ‖B‖ ^ 2) +
        2 * (pq * Real.log (Fintype.card d)) *
          Finset.univ.sup' Finset.univ_nonempty (colNormSq B) +
        2 * (rq * Real.log (Fintype.card n)) *
          Finset.univ.sup' Finset.univ_nonempty
            (fun j => ∑ k, ‖B j k‖ ^ 2) +
        Real.log (Fintype.card d) * Real.log (Fintype.card n) *
          Finset.univ.sup' Finset.univ_nonempty
            (fun j => Finset.univ.sup' Finset.univ_nonempty
              (fun k => ‖B j k‖ ^ 2)) := by
  have h1 := conditional_column_bound (μ₁ := μ₁) (μ₂ := μ₂) (B := B) hrq
    hδmeas hδrange hξmeas hξlaw hξrange hξind
  have h2 := row_sampling_gram_bound (μ₁ := μ₁) (B := B) hpq hδmeas hδlaw
    hδrange hδind
  have h3 := max_column_norm_bound (μ₁ := μ₁) (B := B) hpq hδmeas hδlaw
    hδrange hδind
  have hlogd : 0 ≤ Real.log (Fintype.card d) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hlogn : 0 ≤ Real.log (Fintype.card n) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hB0 : (0 : ℝ) ≤ ‖B‖ ^ 2 := sq_nonneg _
  have hcol0 : (0 : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty
      (colNormSq B) :=
    (colNormSq_nonneg B (Classical.ofNonempty : n)).trans
      (Finset.le_sup' _ (Finset.mem_univ _))
  have hrow0 : (0 : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun j => ∑ k, ‖B j k‖ ^ 2) :=
    (Finset.sum_nonneg fun k _ => by positivity :
        (0 : ℝ) ≤ ∑ k, ‖B (Classical.ofNonempty : d) k‖ ^ 2).trans
      (Finset.le_sup' (f := fun j => ∑ k, ‖B j k‖ ^ 2) (Finset.mem_univ _))
  have hent0 : (0 : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun j => Finset.univ.sup' Finset.univ_nonempty
        (fun k => ‖B j k‖ ^ 2)) := by
    have h4 : (0 : ℝ) ≤ ‖B (Classical.ofNonempty : d)
        (Classical.ofNonempty : n)‖ ^ 2 := by positivity
    have h5 : ‖B (Classical.ofNonempty : d) (Classical.ofNonempty : n)‖ ^ 2 ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun k => ‖B (Classical.ofNonempty : d) k‖ ^ 2) :=
      Finset.le_sup' (f := fun k => ‖B (Classical.ofNonempty : d) k‖ ^ 2)
        (Finset.mem_univ (Classical.ofNonempty : n))
    have h6 : Finset.univ.sup' Finset.univ_nonempty
        (fun k => ‖B (Classical.ofNonempty : d) k‖ ^ 2) ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun j => Finset.univ.sup' Finset.univ_nonempty
            (fun k => ‖B j k‖ ^ 2)) :=
      Finset.le_sup' (f := fun j => Finset.univ.sup' Finset.univ_nonempty
        (fun k => ‖B j k‖ ^ 2)) (Finset.mem_univ _)
    linarith
  refine h1.trans ?_
  have hstep : 1.72 * (rq * ∫ ω₁, lambdaMax
      (Matrix.isHermitian_mul_conjTranspose_self
        (rowSubmatrix B δ ω₁)) ∂μ₁) +
      Real.log (Fintype.card d) *
        ∫ ω₁, Finset.univ.sup' Finset.univ_nonempty
          (colNormSq (rowSubmatrix B δ ω₁)) ∂μ₁ ≤
      1.72 * (rq * (1.72 * (pq * ‖B‖ ^ 2) +
        Real.log (Fintype.card n) * Finset.univ.sup' Finset.univ_nonempty
          (fun j => ∑ k, ‖B j k‖ ^ 2))) +
      Real.log (Fintype.card d) *
        (1.72 * (pq * Finset.univ.sup' Finset.univ_nonempty (colNormSq B)) +
          Real.log (Fintype.card n) * Finset.univ.sup' Finset.univ_nonempty
            (fun j => Finset.univ.sup' Finset.univ_nonempty
              (fun k => ‖B j k‖ ^ 2))) := by
    refine add_le_add ?_ ?_
    · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact mul_le_mul_of_nonneg_left h2 hrq.1
    · exact mul_le_mul_of_nonneg_left h3 hlogd
  refine hstep.trans ?_
  have e1 : 1.72 * (rq * (1.72 * (pq * ‖B‖ ^ 2))) ≤
      3 * (pq * rq * ‖B‖ ^ 2) := by
    have h7 : (0 : ℝ) ≤ pq * rq * ‖B‖ ^ 2 :=
      mul_nonneg (mul_nonneg hpq.1 hrq.1) hB0
    nlinarith
  have e2 : 1.72 * (rq * (Real.log (Fintype.card n) *
      Finset.univ.sup' Finset.univ_nonempty
        (fun j => ∑ k, ‖B j k‖ ^ 2))) ≤
      2 * (rq * Real.log (Fintype.card n)) *
        Finset.univ.sup' Finset.univ_nonempty
          (fun j => ∑ k, ‖B j k‖ ^ 2) := by
    have h8 : (0 : ℝ) ≤ rq * Real.log (Fintype.card n) *
        Finset.univ.sup' Finset.univ_nonempty
          (fun j => ∑ k, ‖B j k‖ ^ 2) :=
      mul_nonneg (mul_nonneg hrq.1 hlogn) hrow0
    nlinarith
  have e3 : Real.log (Fintype.card d) *
      (1.72 * (pq * Finset.univ.sup' Finset.univ_nonempty (colNormSq B))) ≤
      2 * (pq * Real.log (Fintype.card d)) *
        Finset.univ.sup' Finset.univ_nonempty (colNormSq B) := by
    have h9 : (0 : ℝ) ≤ pq * Real.log (Fintype.card d) *
        Finset.univ.sup' Finset.univ_nonempty (colNormSq B) :=
      mul_nonneg (mul_nonneg hpq.1 hlogd) hcol0
    nlinarith
  nlinarith [e1, e2, e3]

end MainBound

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Compression and the second-smallest eigenvalue (Tropp §5.3.3 prerequisite)

The §5.3.3 argument compresses the random Laplacian to the orthogonal
complement of the all-ones vector and asserts (C5-15): "the Courant–Fischer
theorem implies that the minimum eigenvalue of `Y = RΔR*` coincides with the
second-smallest eigenvalue of `Δ` because the smallest eigenvalue of `Δ` has
eigenvector `e`."

* `sortedEigenvalues`/`secondSmallestEigenvalue` — the weakly increasing
  arrangement of the eigenvalues (via `Tuple.sort`) and its second entry;
* `eigenvalues_multiset_compression` — the spectrum splits:
  for Hermitian `A` with a unit null vector `v` and a partial isometry `R`
  (`RR* = 1`, `Rv = 0`, `card W + 1 = card V`),
  `spectrum(A) = {0} + spectrum(RAR*)` as multisets.  Proof: extend `R` by the
  row `v*` to a unitary `U`, compute `UAU* = fromBlocks 0 0 0 (RAR*)`, and
  compare characteristic polynomials (`charpoly_units_conj`,
  `charpoly_fromBlocks_zero₂₁`, `roots_charpoly_eq_eigenvalues`);
* `lambdaMin_compression_eq_secondSmallest` — for psd `A`, the identification
  `λ_min(RAR*) = λ₂↑(A)` (sorted-list comparison);
* `exists_compression_isometry` — the hidden existence obligation for the
  partial isometry `R` (§5.3.3 "we introduce an `(n−1) × n` partial isometry
  `R`"), via an orthonormal basis of `(span v)ᗮ`
  (`OrthonormalBasis.fromOrthogonalSpanSingleton`);
* `conjTranspose_mul_self_eq_one_sub` — `R*R = 1 − vv*` (the compression
  projector), and the psd-kernel fact `mulVec_eq_zero_of_dotProduct_eq_zero`
  (`x*Mx = 0 → Mx = 0` for psd `M`), both needed by the connectivity
  characterization in the next file.

-/

namespace MatrixConcentration

open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {W : Type*} [Fintype W] [DecidableEq W]

section SortedEigenvalues

variable {A : Matrix V V ℂ}

/-- **Book §2.1.6 and §5.3.1–§5.3.3**: the weakly increasing arrangement of
the eigenvalues of a Hermitian matrix, written `λ₁↑ ≤ λ₂↑ ≤ …`. -/
noncomputable def sortedEigenvalues (hA : A.IsHermitian) :
    Fin (Fintype.card V) → ℝ :=
  let f := hA.eigenvalues ∘ (Fintype.equivFin V).symm
  f ∘ Tuple.sort f

/-- Lean implementation helper: monotonicity of the sorted eigenvalue arrangement. -/
lemma sortedEigenvalues_monotone (hA : A.IsHermitian) :
    Monotone (sortedEigenvalues hA) :=
  Tuple.monotone_sort _

/-- Lean implementation helper: the sorted arrangement enumerates the eigenvalue multiset. -/
lemma sortedEigenvalues_multiset_eq (hA : A.IsHermitian) :
    Multiset.map (sortedEigenvalues hA) Finset.univ.val =
      Multiset.map hA.eigenvalues Finset.univ.val := by
  classical
  rw [sortedEigenvalues]
  have h1 : Multiset.map ((hA.eigenvalues ∘ (Fintype.equivFin V).symm) ∘
      Tuple.sort (hA.eigenvalues ∘ (Fintype.equivFin V).symm)) Finset.univ.val =
      Multiset.map (hA.eigenvalues ∘ (Fintype.equivFin V).symm)
        (Multiset.map (Tuple.sort (hA.eigenvalues ∘ (Fintype.equivFin V).symm))
          Finset.univ.val) := by
    rw [Multiset.map_map]
  rw [h1]
  have h2 : Multiset.map
      (⇑(Tuple.sort (hA.eigenvalues ∘ (Fintype.equivFin V).symm)))
      Finset.univ.val = Finset.univ.val := by
    have := Finset.map_univ_equiv
      (Tuple.sort (hA.eigenvalues ∘ (Fintype.equivFin V).symm) :
        Fin (Fintype.card V) ≃ Fin (Fintype.card V))
    calc Multiset.map _ Finset.univ.val
        = (Finset.univ.map (Tuple.sort (hA.eigenvalues ∘
            (Fintype.equivFin V).symm)).toEmbedding).val := rfl
    _ = Finset.univ.val := by rw [this]
  rw [h2]
  have h3 : Multiset.map (hA.eigenvalues ∘ (Fintype.equivFin V).symm)
      Finset.univ.val = Multiset.map hA.eigenvalues
        (Multiset.map (⇑(Fintype.equivFin V).symm) Finset.univ.val) := by
    rw [Multiset.map_map]
  rw [h3]
  have h4 : Multiset.map (⇑(Fintype.equivFin V).symm) Finset.univ.val =
      Finset.univ.val := by
    have := Finset.map_univ_equiv ((Fintype.equivFin V).symm)
    calc Multiset.map _ Finset.univ.val
        = (Finset.univ.map ((Fintype.equivFin V).symm).toEmbedding).val := rfl
    _ = Finset.univ.val := by rw [this]
  rw [h4]

/-- Lean implementation helper: each sorted value is an eigenvalue, and each eigenvalue appears in the
sorted arrangement. -/
lemma sortedEigenvalues_exists (hA : A.IsHermitian) (i : Fin (Fintype.card V)) :
    ∃ v, sortedEigenvalues hA i = hA.eigenvalues v :=
  ⟨(Fintype.equivFin V).symm (Tuple.sort _ i), rfl⟩

/-- Lean implementation helper: every eigenvalue occurs in the sorted arrangement. -/
lemma exists_sortedEigenvalues_eq (hA : A.IsHermitian) (v : V) :
    ∃ i, sortedEigenvalues hA i = hA.eigenvalues v := by
  refine ⟨(Tuple.sort (hA.eigenvalues ∘ (Fintype.equivFin V).symm)).symm
    (Fintype.equivFin V v), ?_⟩
  rw [sortedEigenvalues]
  show (hA.eigenvalues ∘ (Fintype.equivFin V).symm)
    (Tuple.sort _ ((Tuple.sort _).symm (Fintype.equivFin V v))) = _
  rw [Equiv.apply_symm_apply]
  show hA.eigenvalues ((Fintype.equivFin V).symm (Fintype.equivFin V v)) = _
  rw [Equiv.symm_apply_apply]

/-- Lean implementation helper: the first sorted eigenvalue is `λ_min`. -/
lemma sortedEigenvalues_zero [Nonempty V] (hA : A.IsHermitian) :
    sortedEigenvalues hA ⟨0, Fintype.card_pos⟩ = lambdaMin hA := by
  refine le_antisymm ?_ ?_
  · refine le_lambdaMin hA fun v => ?_
    obtain ⟨i, hi⟩ := exists_sortedEigenvalues_eq hA v
    rw [← hi]
    exact sortedEigenvalues_monotone hA (by simp [Fin.le_def])
  · obtain ⟨v, hv⟩ := sortedEigenvalues_exists hA ⟨0, Fintype.card_pos⟩
    rw [hv]
    exact lambdaMin_le_eigenvalues hA v

/-- **Book §2.1.6 and §5.3.1–§5.3.3**: the second-smallest eigenvalue `λ₂↑`,
implemented as the second entry of the sorted arrangement and totalized to `0`
in dimension less than two. -/
noncomputable def secondSmallestEigenvalue (hA : A.IsHermitian) : ℝ :=
  if h : 1 < Fintype.card V then sortedEigenvalues hA ⟨1, h⟩ else 0

/-- Lean implementation helper: evaluation of `secondSmallestEigenvalue` in dimension at least two. -/
lemma secondSmallestEigenvalue_eq (hA : A.IsHermitian)
    (h : 1 < Fintype.card V) :
    secondSmallestEigenvalue hA = sortedEigenvalues hA ⟨1, h⟩ :=
  dif_pos h

end SortedEigenvalues

section CompressionAlgebra

variable {A : Matrix V V ℂ}

/-- Lean implementation helper: a single-row matrix. -/
def rowVec (v : V → ℂ) : Matrix Unit V ℂ := Matrix.of fun _ j => v j

/-- Lean implementation helper: a single-column matrix. -/
def colVec (v : V → ℂ) : Matrix V Unit ℂ := Matrix.of fun j _ => v j

/-- Lean implementation helper: conjugate transpose of a one-row matrix. -/
lemma conjTranspose_rowVec (v : V → ℂ) : (rowVec v)ᴴ = colVec (star v) := by
  ext j u
  rfl

/-- Lean implementation helper: multiplication of a one-row matrix on the right. -/
lemma rowVec_mul {m' : Type*} [Fintype m'] (v : V → ℂ) (M : Matrix V m' ℂ) :
    rowVec v * M = Matrix.of fun _ j => (v ᵥ* M) j := by
  ext u j
  rw [Matrix.mul_apply]
  rfl

/-- Lean implementation helper: multiplication by a one-column matrix on the right. -/
lemma mul_colVec {m' : Type*} [Fintype m'] [DecidableEq m']
    (M : Matrix m' V ℂ) (v : V → ℂ) :
    M * colVec v = colVec (M *ᵥ v) := by
  ext i u
  rw [Matrix.mul_apply]
  rfl

/-- Lean implementation helper: product of a one-row and a one-column matrix. -/
lemma rowVec_mul_colVec (v w : V → ℂ) :
    rowVec v * colVec w = Matrix.of fun _ _ : Unit => v ⬝ᵥ w := by
  ext u u'
  rw [Matrix.mul_apply]
  rfl

/-- Lean implementation helper: the row representation of the zero vector is zero. -/
lemma rowVec_zero : rowVec (0 : V → ℂ) = 0 := by
  ext u j
  rfl

/-- Lean implementation helper: the column representation of the zero vector is zero. -/
lemma colVec_zero : colVec (0 : V → ℂ) = 0 := by
  ext j u
  rfl

variable {R : Matrix W V ℂ}

/-- Lean implementation helper: the unitary extension of the partial isometry —
stack the row `v*` on top of `R`. -/
noncomputable def stackedUnitary (v : V → ℂ) (R : Matrix W V ℂ) :
    Matrix (Unit ⊕ W) V ℂ :=
  Matrix.fromRows (rowVec (star v)) R

/-- Lean implementation helper: the stacked matrix is a co-isometry, `U U* = 1`. -/
lemma stackedUnitary_mul_conjTranspose {v : V → ℂ} (hv : l2norm v = 1)
    (hRR : R * Rᴴ = 1) (hRv : R *ᵥ v = 0) :
    stackedUnitary v R * (stackedUnitary v R)ᴴ = 1 := by
  rw [stackedUnitary, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromRows_mul_fromCols]
  rw [conjTranspose_rowVec, star_star]
  -- the four blocks
  have h11 : rowVec (star v) * colVec v = 1 := by
    rw [rowVec_mul_colVec]
    ext u u'
    have h1 : star v ⬝ᵥ v = ((l2norm v ^ 2 : ℝ) : ℂ) := dotProduct_star_self_eq v
    rw [Matrix.of_apply, h1, hv]
    norm_num
  have h12 : rowVec (star v) * Rᴴ = 0 := by
    have h1 : star v ᵥ* Rᴴ = star (R *ᵥ v) := (Matrix.star_mulVec R v).symm
    rw [rowVec_mul]
    ext u j
    rw [Matrix.of_apply, h1, hRv]
    simp
  have h21 : R * colVec v = 0 := by
    rw [mul_colVec, hRv, colVec_zero]
  rw [h11, h12, h21, hRR]
  exact Matrix.fromBlocks_one

/-- Lean implementation helper: the conjugated matrix has the block form
`[[0, 0], [0, RAR*]]` when `v` is a null vector of the Hermitian matrix `A`. -/
lemma stackedUnitary_conj_eq_fromBlocks (hA : A.IsHermitian) {v : V → ℂ}
    (hAv : A *ᵥ v = 0) (R : Matrix W V ℂ) :
    stackedUnitary v R * A * (stackedUnitary v R)ᴴ =
      Matrix.fromBlocks 0 0 0 (R * A * Rᴴ) := by
  rw [stackedUnitary, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_rowVec, star_star, Matrix.fromRows_mul,
    Matrix.fromRows_mul_fromCols]
  have hvA : star v ᵥ* A = 0 := by
    have h1 : star (A *ᵥ v) = star v ᵥ* Aᴴ := Matrix.star_mulVec A v
    rw [hAv, star_zero] at h1
    rw [← hA.eq]
    exact h1.symm
  have hrvA : rowVec (star v) * A = 0 := by
    rw [rowVec_mul, hvA]
    ext u j
    rfl
  have h11 : rowVec (star v) * A * colVec v = 0 := by
    rw [hrvA, Matrix.zero_mul]
  have h12 : rowVec (star v) * A * Rᴴ = 0 := by
    rw [hrvA, Matrix.zero_mul]
  have h21 : R * A * colVec v = 0 := by
    rw [Matrix.mul_assoc, mul_colVec, hAv, colVec_zero, Matrix.mul_zero]
  rw [h11, h12, h21]

/-- Lean implementation helper: the characteristic polynomial of the `1 × 1`
zero matrix is `X`. -/
lemma charpoly_zero_unit : (0 : Matrix Unit Unit ℂ).charpoly = Polynomial.X := by
  rw [Matrix.charpoly, Matrix.det_unique]
  simp [Matrix.charmatrix_apply_eq]

/-- **Book §5.3.3 (C5-15), spectrum splitting**: for a Hermitian matrix `A` with
unit null vector `v` and a partial isometry `R` with `RR* = 1`, `Rv = 0`, and
`card W + 1 = card V`, the eigenvalue multiset of `A` is `{0}` together with the
eigenvalue multiset of the compression `RAR*`.  Implicit source declaration
(the content of the Courant–Fischer remark).

**Author note.** This full multiset identity is stronger than the
second-smallest/minimum-eigenvalue identification used in the Book. -/
theorem eigenvalues_multiset_compression (hA : A.IsHermitian) {v : V → ℂ}
    (hv : l2norm v = 1) (hAv : A *ᵥ v = 0) {R : Matrix W V ℂ}
    (hRR : R * Rᴴ = 1) (hRv : R *ᵥ v = 0)
    (hcard : Fintype.card W + 1 = Fintype.card V)
    (hRAR : (R * A * Rᴴ).IsHermitian) :
    Multiset.map hA.eigenvalues Finset.univ.val =
      0 ::ₘ Multiset.map hRAR.eigenvalues Finset.univ.val := by
  classical
  -- the reindexing equivalence
  have hcard' : Fintype.card (Unit ⊕ W) = Fintype.card V := by
    simp [Fintype.card_sum]
    omega
  let e : (Unit ⊕ W) ≃ V := Fintype.equivOfCardEq hcard'
  set U : Matrix (Unit ⊕ W) V ℂ := stackedUnitary v R with hUdef
  have hUU : U * Uᴴ = 1 := stackedUnitary_mul_conjTranspose hv hRR hRv
  -- square version
  set U' : Matrix V V ℂ := (Matrix.reindex e (Equiv.refl V)) U with hU'def
  have hU'U' : U' * U'ᴴ = 1 := by
    rw [hU'def]
    have h1 : (Matrix.reindex e (Equiv.refl V)) U =
        U.submatrix ⇑e.symm ⇑(Equiv.refl V) := by
      rw [Matrix.reindex_apply, Equiv.refl_symm]
    rw [h1, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv U Uᴴ ⇑e.symm (Equiv.refl V) ⇑e.symm, hUU]
    exact Matrix.submatrix_one_equiv e.symm
  have hU'U'2 : U'ᴴ * U' = 1 := mul_eq_one_comm.mp hU'U'
  -- the unit and the conjugation-invariance of the charpoly
  let Uu : (Matrix V V ℂ)ˣ := ⟨U', U'ᴴ, hU'U', hU'U'2⟩
  have hconj : (U' * A * U'ᴴ).charpoly = A.charpoly := by
    have h := Matrix.charpoly_units_conj Uu A
    have h2 : (↑Uu : Matrix V V ℂ) = U' := rfl
    rw [h2] at h
    have h3 : U'⁻¹ = U'ᴴ := Matrix.inv_eq_right_inv hU'U'
    rw [h3] at h
    exact h
  -- identify the conjugation with the reindexed block matrix
  have hblock : U' * A * U'ᴴ = (Matrix.reindex e e)
      (Matrix.fromBlocks 0 0 0 (R * A * Rᴴ)) := by
    rw [hU'def]
    have h1 : (Matrix.reindex e (Equiv.refl V)) U =
        U.submatrix ⇑e.symm ⇑(Equiv.refl V) := by
      rw [Matrix.reindex_apply, Equiv.refl_symm]
    rw [h1, Matrix.conjTranspose_submatrix]
    have h2 : U.submatrix (⇑e.symm) ⇑(Equiv.refl V) * A =
        (U * A).submatrix ⇑e.symm ⇑(Equiv.refl V) := by
      have h2' := Matrix.submatrix_mul_equiv U
        (A.submatrix ⇑(Equiv.refl V) ⇑(Equiv.refl V)) ⇑e.symm (Equiv.refl V)
        ⇑(Equiv.refl V)
      simpa using h2'
    rw [h2]
    have h3 : (U * A).submatrix (⇑e.symm) ⇑(Equiv.refl V) *
        Uᴴ.submatrix ⇑(Equiv.refl V) ⇑e.symm =
        (U * A * Uᴴ).submatrix ⇑e.symm ⇑e.symm := by
      have h3' := Matrix.submatrix_mul_equiv (U * A) Uᴴ ⇑e.symm (Equiv.refl V)
        ⇑e.symm
      simpa using h3'
    rw [h3, stackedUnitary_conj_eq_fromBlocks hA hAv R]
    rfl
  -- charpoly of the block matrix
  have hcharblock : (Matrix.fromBlocks (0 : Matrix Unit Unit ℂ) 0 0
      (R * A * Rᴴ)).charpoly = Polynomial.X * (R * A * Rᴴ).charpoly := by
    rw [Matrix.charpoly_fromBlocks_zero₂₁, charpoly_zero_unit]
  have hchar : A.charpoly = Polynomial.X * (R * A * Rᴴ).charpoly := by
    rw [← hconj, hblock]
    have h4 := Matrix.charpoly_reindex e
      (Matrix.fromBlocks (0 : Matrix Unit Unit ℂ) 0 0 (R * A * Rᴴ))
    rw [show Matrix.reindex e e = Matrix.reindex e e from rfl] at h4
    rw [h4, hcharblock]
  -- pass to roots
  have hrootsA := hA.roots_charpoly_eq_eigenvalues
  have hrootsC := hRAR.roots_charpoly_eq_eigenvalues
  have hXne : (Polynomial.X : Polynomial ℂ) ≠ 0 := Polynomial.X_ne_zero
  have hCne : (R * A * Rᴴ).charpoly ≠ 0 := (R * A * Rᴴ).charpoly_monic.ne_zero
  have hroots : A.charpoly.roots =
      0 ::ₘ (R * A * Rᴴ).charpoly.roots := by
    rw [hchar, Polynomial.roots_mul (mul_ne_zero hXne hCne),
      Polynomial.roots_X]
    rfl
  rw [hrootsA, hrootsC] at hroots
  -- strip the `ofReal` coercion
  have hinj : Function.Injective (RCLike.ofReal : ℝ → ℂ) :=
    RCLike.ofReal_injective
  have h5 : Multiset.map (RCLike.ofReal : ℝ → ℂ)
      (Multiset.map hA.eigenvalues Finset.univ.val) =
      Multiset.map (RCLike.ofReal : ℝ → ℂ)
        (0 ::ₘ Multiset.map hRAR.eigenvalues Finset.univ.val) := by
    rw [Multiset.map_cons, Multiset.map_map, Multiset.map_map]
    rw [show ((RCLike.ofReal : ℝ → ℂ) 0) = 0 from by norm_num]
    exact hroots
  exact Multiset.map_injective hinj h5

end CompressionAlgebra

section Identification

variable {A : Matrix V V ℂ} {R : Matrix W V ℂ}

/-- Lean implementation helper: the sorted arrangement, as a sorted list. -/
lemma ofFn_sortedEigenvalues_sortedLE (hA : A.IsHermitian) :
    (List.ofFn (sortedEigenvalues hA)).SortedLE :=
  List.sortedLE_ofFn_iff.mpr (sortedEigenvalues_monotone hA)

/-- Lean implementation helper: the sorted list carries the eigenvalue
multiset. -/
lemma ofFn_sortedEigenvalues_coe (hA : A.IsHermitian) :
    (↑(List.ofFn (sortedEigenvalues hA)) : Multiset ℝ) =
      Multiset.map hA.eigenvalues Finset.univ.val := by
  rw [← Fin.univ_val_map]
  exact sortedEigenvalues_multiset_eq hA

/-- **Book §5.3.3 (C5-15)**: "the Courant–Fischer theorem implies that the
minimum eigenvalue of `Y` coincides with the second-smallest eigenvalue of `Δ`
because the smallest eigenvalue of `Δ` has eigenvector `e`" — for a psd matrix
`A` with unit null vector `v` and a partial isometry `R` annihilating `v`,
`λ_min(RAR*) = λ₂↑(A)`. Implicit source declaration. -/
theorem lambdaMin_compression_eq_secondSmallest [Nonempty W]
    (hpsd : A.PosSemidef) {v : V → ℂ}
    (hv : l2norm v = 1) (hAv : A *ᵥ v = 0)
    (hRR : R * Rᴴ = 1) (hRv : R *ᵥ v = 0)
    (hcard : Fintype.card W + 1 = Fintype.card V)
    (hRAR : (R * A * Rᴴ).IsHermitian) :
    lambdaMin hRAR = secondSmallestEigenvalue hpsd.1 := by
  classical
  have hWpos : 0 < Fintype.card W := Fintype.card_pos
  have hcard1 : 1 < Fintype.card V := by omega
  have hNV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hCpsd : (R * A * Rᴴ).PosSemidef := hpsd.mul_mul_conjTranspose_same R
  have hmult := eigenvalues_multiset_compression hpsd.1 hv hAv hRR hRv hcard hRAR
  -- the sorted lists agree
  have hkey : List.ofFn (sortedEigenvalues hpsd.1) =
      0 :: List.ofFn (sortedEigenvalues hRAR) := by
    have hperm : (↑(List.ofFn (sortedEigenvalues hpsd.1)) : Multiset ℝ) =
        ↑(0 :: List.ofFn (sortedEigenvalues hRAR)) := by
      rw [ofFn_sortedEigenvalues_coe, hmult]
      rw [show ((0 : ℝ) :: List.ofFn (sortedEigenvalues hRAR) : Multiset ℝ) =
        0 ::ₘ ↑(List.ofFn (sortedEigenvalues hRAR)) from rfl,
        ofFn_sortedEigenvalues_coe]
    have hsorted2 : ((0 : ℝ) :: List.ofFn (sortedEigenvalues hRAR)).SortedLE := by
      rw [List.sortedLE_iff_pairwise, List.pairwise_cons]
      constructor
      · intro x hx
        rw [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨w, hw⟩ := sortedEigenvalues_exists hRAR i
        rw [hw]
        exact hCpsd.eigenvalues_nonneg w
      · rw [← List.sortedLE_iff_pairwise]
        exact ofFn_sortedEigenvalues_sortedLE hRAR
    exact (Multiset.coe_eq_coe.mp hperm).eq_of_sortedLE
      (ofFn_sortedEigenvalues_sortedLE hpsd.1) hsorted2
  -- read off the second entry via `getD`
  rw [secondSmallestEigenvalue_eq hpsd.1 hcard1]
  have h5 := congrArg (fun l : List ℝ => l.getD 1 0) hkey
  simp only [List.getD_cons_succ] at h5
  have hL : (List.ofFn (sortedEigenvalues hpsd.1)).getD 1 0 =
      sortedEigenvalues hpsd.1 ⟨1, hcard1⟩ := by
    have hlen : 1 < (List.ofFn (sortedEigenvalues hpsd.1)).length := by
      simp
      omega
    rw [List.getD_eq_getElem _ _ hlen, List.getElem_ofFn]
  have hR : (List.ofFn (sortedEigenvalues hRAR)).getD 0 0 =
      sortedEigenvalues hRAR ⟨0, Fintype.card_pos⟩ := by
    have hlen : 0 < (List.ofFn (sortedEigenvalues hRAR)).length := by
      simp
      exact Fintype.card_pos
    rw [List.getD_eq_getElem _ _ hlen, List.getElem_ofFn]
  rw [hL, hR] at h5
  rw [h5, sortedEigenvalues_zero hRAR]

end Identification

section ProjectorAndKernel

variable {A : Matrix V V ℂ} {R : Matrix W V ℂ}

/-- Lean implementation helper: the complementary projector identity
`R*R = 1 − vv*` for the partial isometry of §5.3.3 (needed by the connectivity
characterization). -/
theorem conjTranspose_mul_self_eq_one_sub {v : V → ℂ}
    (hv : l2norm v = 1) (hRR : R * Rᴴ = 1) (hRv : R *ᵥ v = 0)
    (hcard : Fintype.card W + 1 = Fintype.card V) :
    Rᴴ * R = 1 - Matrix.of (fun i j => v i * star (v j)) := by
  classical
  have hcard' : Fintype.card (Unit ⊕ W) = Fintype.card V := by
    simp [Fintype.card_sum]
    omega
  let e : (Unit ⊕ W) ≃ V := Fintype.equivOfCardEq hcard'
  set U : Matrix (Unit ⊕ W) V ℂ := stackedUnitary v R with hUdef
  have hUU : U * Uᴴ = 1 := stackedUnitary_mul_conjTranspose hv hRR hRv
  set U' : Matrix V V ℂ := (Matrix.reindex e (Equiv.refl V)) U with hU'def
  have hU'U' : U' * U'ᴴ = 1 := by
    rw [hU'def]
    have h1 : (Matrix.reindex e (Equiv.refl V)) U =
        U.submatrix ⇑e.symm ⇑(Equiv.refl V) := by
      rw [Matrix.reindex_apply, Equiv.refl_symm]
    rw [h1, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv U Uᴴ ⇑e.symm (Equiv.refl V) ⇑e.symm, hUU]
    exact Matrix.submatrix_one_equiv e.symm
  have hU'U'2 : U'ᴴ * U' = 1 := mul_eq_one_comm.mp hU'U'
  -- transport back: `U*U = U'*U'` after unreindexing
  have hUtU : Uᴴ * U = 1 := by
    have h1 : (Matrix.reindex e (Equiv.refl V)) U =
        U.submatrix ⇑e.symm ⇑(Equiv.refl V) := by
      rw [Matrix.reindex_apply, Equiv.refl_symm]
    rw [hU'def, h1, Matrix.conjTranspose_submatrix] at hU'U'2
    have h2 := Matrix.submatrix_mul_equiv Uᴴ U ⇑(Equiv.refl V) e.symm
      ⇑(Equiv.refl V)
    rw [h2] at hU'U'2
    have h3 : (Uᴴ * U).submatrix ⇑(Equiv.refl V) ⇑(Equiv.refl V) = Uᴴ * U := by
      rw [show ⇑(Equiv.refl V) = id from rfl, Matrix.submatrix_id_id]
    rw [h3] at hU'U'2
    exact hU'U'2
  -- decompose `U*U`
  have hdecomp : Uᴴ * U =
      colVec v * rowVec (star v) + Rᴴ * R := by
    rw [hUdef, stackedUnitary, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, conjTranspose_rowVec, star_star]
  have houter : colVec v * rowVec (star v) =
      Matrix.of (fun i j => v i * star (v j)) := by
    ext i j
    rw [Matrix.mul_apply]
    simp [colVec, rowVec]
  rw [hdecomp, houter] at hUtU
  rw [← hUtU]
  abel

/-- Lean implementation helper (psd kernel characterization): if `M ≽ 0` and
`x*Mx = 0`, then `Mx = 0` (write `M = B*B`, so `x*Mx = ‖Bx‖²`).  Needed by the
connectivity characterization of §5.3.1. -/
theorem mulVec_eq_zero_of_dotProduct_eq_zero {M : Matrix V V ℂ}
    (hM : M.PosSemidef) {x : V → ℂ} (h : star x ⬝ᵥ (M *ᵥ x) = 0) :
    M *ᵥ x = 0 := by
  classical
  have hray : rayleigh M x = 0 := by
    have h1 := star_dotProduct_mulVec_eq_rayleigh hM.1 x
    rw [h] at h1
    exact_mod_cast h1.symm
  rw [rayleigh_eq_sum hM.1 x] at hray
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ hM.1.eigenvalues i *
      ‖((hM.1.eigenvectorUnitary : Matrix V V ℂ)ᴴ *ᵥ x) i‖ ^ 2 := fun i _ =>
    mul_nonneg (hM.eigenvalues_nonneg i) (by positivity)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hray
  have hM_eq := spectral_decomposition hM.1
  rw [show M *ᵥ x = ((hM.1.eigenvectorUnitary : Matrix V V ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) *
      (hM.1.eigenvectorUnitary : Matrix V V ℂ)ᴴ) *ᵥ x from by rw [← hM_eq]]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hDx : Matrix.diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) *ᵥ
      ((hM.1.eigenvectorUnitary : Matrix V V ℂ)ᴴ *ᵥ x) = 0 := by
    funext i
    show (Matrix.diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) *ᵥ
      ((hM.1.eigenvectorUnitary : Matrix V V ℂ)ᴴ *ᵥ x)) i = (0 : ℂ)
    rw [Matrix.mulVec_diagonal]
    show (RCLike.ofReal (hM.1.eigenvalues i) : ℂ) *
      ((hM.1.eigenvectorUnitary : Matrix V V ℂ)ᴴ *ᵥ x) i = 0
    rcases mul_eq_zero.mp (hterm i (Finset.mem_univ i)) with h1 | h1
    · rw [h1]
      simp
    · have h2 : ‖((hM.1.eigenvectorUnitary : Matrix V V ℂ)ᴴ *ᵥ x) i‖ = 0 := by
        nlinarith [norm_nonneg (((hM.1.eigenvectorUnitary : Matrix V V ℂ)ᴴ *ᵥ x) i)]
      rw [norm_eq_zero.mp h2, mul_zero]
  rw [hDx, Matrix.mulVec_zero]

/-- **Book §5.3.3 hidden existence obligation** ("we introduce an
`(n−1) × n` partial isometry `R` that satisfies (5.3.3)"): for every unit
vector `v` there is a partial isometry `R` with `RR* = 1` and `Rv = 0` —
rows given by an orthonormal basis of `(span v)ᗮ`.  Implicit source
declaration. -/
theorem exists_compression_isometry [Nonempty V] {v : V → ℂ}
    (hv : l2norm v = 1) :
    ∃ R : Matrix (Fin (Fintype.card V - 1)) V ℂ,
      R * Rᴴ = 1 ∧ R *ᵥ v = 0 := by
  classical
  set v' : EuclideanSpace ℂ V := WithLp.toLp 2 v with hv'def
  have hv'norm : ‖v'‖ = 1 := hv
  have hv'ne : v' ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv'norm
    norm_num at hv'norm
  have hfact : Fact (Module.finrank ℂ (EuclideanSpace ℂ V) =
      (Fintype.card V - 1) + 1) := ⟨by
    rw [finrank_euclideanSpace]
    have := Fintype.card_pos (α := V)
    omega⟩
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton
    (𝕜 := ℂ) (Fintype.card V - 1) hv'ne
  refine ⟨Matrix.of (fun w j => star (((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j)),
    ?_, ?_⟩
  · -- `RR* = 1` from orthonormality of the rows
    ext w w'
    rw [Matrix.mul_apply]
    have h1 : ∀ j, Matrix.of (fun w j =>
        star (((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j)) w j *
        (Matrix.of (fun w j =>
          star (((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j)))ᴴ j w' =
        star (((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j) *
          ((b w' : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j := by
      intro j
      rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply,
        star_star]
    rw [Finset.sum_congr rfl fun j _ => h1 j]
    have h2 : inner ℂ ((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V)
        ((b w' : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) =
        star (fun j => ((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j) ⬝ᵥ
          (fun j => ((b w' : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j) :=
      inner_toLp_eq_dotProduct _ _
    rw [show (∑ j, star (((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j) *
        ((b w' : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j) =
        star (fun j => ((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j) ⬝ᵥ
          (fun j => ((b w' : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j) from rfl, ← h2]
    have h3 := b.orthonormal
    rw [orthonormal_iff_ite] at h3
    have h4 := h3 w w'
    rw [show (inner ℂ (b w) (b w') : ℂ) =
      inner ℂ ((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V)
        ((b w' : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) from rfl] at h4
    rw [h4, Matrix.one_apply]
  · -- `Rv = 0` since the rows are orthogonal to `v`
    funext w
    show (∑ j, star (((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j) * v j) = 0
    have h1 : inner ℂ ((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) v' =
        star (fun j => ((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j) ⬝ᵥ v :=
      inner_toLp_eq_dotProduct _ _
    rw [show (∑ j, star (((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j) * v j) =
        star (fun j => ((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) j) ⬝ᵥ v from rfl,
      ← h1]
    have h2 : ((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) ∈ (ℂ ∙ v')ᗮ := (b w).2
    rw [Submodule.mem_orthogonal] at h2
    have h3 := h2 v' (Submodule.mem_span_singleton_self v')
    calc inner ℂ ((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V) v'
        = starRingEnd ℂ (inner ℂ v' ((b w : (ℂ ∙ v')ᗮ) : EuclideanSpace ℂ V)) :=
        (inner_conj_symm _ _).symm
    _ = 0 := by rw [h3]; simp

end ProjectorAndKernel

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Graph Laplacians and connectivity (Tropp §5.3.1)

Formalizes the graph-theoretic material of §5.3.1 (C5-12, C5-13):

* the correspondence between the book's combinatorial definitions (adjacency
  matrix, degree, Laplacian `Δ = D − A`) and Mathlib's `SimpleGraph.adjMatrix`,
  `SimpleGraph.degMatrix`, `SimpleGraph.lapMatrix` — the definitions match the
  book verbatim, so we work with `lapMatrixC G = (G.lapMatrix ℝ).map ofReal`,
  the book's Laplacian read as a complex Hermitian matrix (the book treats all
  matrices in `𝕄_n(ℂ)`);
* `posSemidef_lapMatrixC` — "each Laplacian matrix is positive semidefinite"
  (book §5.3.1), transported from Mathlib's real statement through the
  quadratic-form bridge `posSemidef_map_ofReal`;
* `lapMatrixC_mulVec_one_eq_zero` — "the vector `e` of ones is always an
  eigenvector of `Δ` with eigenvalue zero" (book §5.3.1);
* `normalizedLapMatrix` — the book's normalized Laplacian
  `H = D^{−1/2} Δ D^{−1/2}` "where we place the convention that `0^{−1/2} = 0`"
  (the convention is automatic for `Real.rpow`); the book makes no claim about
  `H`, so this is a definition only;
* `connected_iff_secondSmallest_pos` (**C5-13**) — "the graph `G` is connected
  if and only if the second-smallest eigenvalue of `Δ` is strictly positive,"
  established using Mathlib's kernel description
  `lapMatrix_mulVec_eq_zero_iff_forall_reachable`
  together with the compression machinery of the previous file.
-/

namespace MatrixConcentration

open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V]

section ComplexificationBridge

/-- Lean implementation helper: the complexification of a real symmetric matrix
is Hermitian. -/
lemma isHermitian_map_ofReal {M : Matrix V V ℝ} (hM : M.IsHermitian) :
    (M.map (Complex.ofReal)).IsHermitian := by
  have h : (M.map (Complex.ofReal))ᴴ = M.map (Complex.ofReal) := by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply,
      Complex.star_def, Complex.conj_ofReal]
    rw [show M j i = M i j from by
      have h1 := congrFun (congrFun hM i) j
      rw [Matrix.conjTranspose_apply, star_trivial] at h1
      exact h1]
  exact h

/-- Lean implementation helper: the quadratic form of a complexified real
matrix splits into the real quadratic forms of the real and imaginary parts. -/
lemma rayleigh_map_ofReal (M : Matrix V V ℝ) (x : V → ℂ) :
    rayleigh (M.map (Complex.ofReal)) x =
      ((fun i => (x i).re) ⬝ᵥ (M *ᵥ fun k => (x k).re)) +
        ((fun i => (x i).im) ⬝ᵥ (M *ᵥ fun k => (x k).im)) := by
  classical
  have hterm : ∀ i, (star x i * ((M.map (Complex.ofReal)) *ᵥ x) i).re =
      (x i).re * (M *ᵥ fun k => (x k).re) i +
        (x i).im * (M *ᵥ fun k => (x k).im) i := by
    intro i
    show (star (x i) * ((M.map (Complex.ofReal)) *ᵥ x) i).re = _
    rw [Matrix.mulVec, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
      dotProduct, Finset.mul_sum, Complex.re_sum, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.map_apply, Complex.star_def]
    simp [Complex.mul_re, Complex.mul_im]
  rw [rayleigh, dotProduct, Complex.re_sum,
    Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
  rfl

/-- Lean implementation helper: complexification preserves positive
semidefiniteness. -/
lemma posSemidef_map_ofReal {M : Matrix V V ℝ} (hM : M.PosSemidef) :
    (M.map (Complex.ofReal)).PosSemidef := by
  refine posSemidef_iff_isHermitian_quadratic.mpr
    ⟨isHermitian_map_ofReal hM.1, fun u => ?_⟩
  have h : (star u ⬝ᵥ ((M.map (Complex.ofReal)) *ᵥ u)).re =
      rayleigh (M.map (Complex.ofReal)) u := rfl
  rw [h, rayleigh_map_ofReal M u]
  have ha := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM).2
    (fun i => (u i).re)
  have hb := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM).2
    (fun i => (u i).im)
  rw [star_trivial] at ha hb
  linarith

/-- Lean implementation helper: complexified matrix–vector products of real
vectors. -/
lemma map_mulVec_ofReal (M : Matrix V V ℝ) (x : V → ℝ) :
    (M.map (Complex.ofReal)) *ᵥ (fun i => ((x i : ℝ) : ℂ)) =
      fun i => (((M *ᵥ x) i : ℝ) : ℂ) := by
  funext i
  show ∑ k, (M.map (Complex.ofReal)) i k * (x k : ℂ) = (((M *ᵥ x) i : ℝ) : ℂ)
  rw [show ((M *ᵥ x) i : ℝ) = ∑ k, M i k * x k from rfl]
  push_cast
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.map_apply]

/-- Lean implementation helper: real part of a complexified matrix–vector
product. -/
lemma re_map_mulVec (M : Matrix V V ℝ) (x : V → ℂ) (i : V) :
    (((M.map (Complex.ofReal)) *ᵥ x) i).re = (M *ᵥ fun k => (x k).re) i := by
  show (∑ k, (M.map (Complex.ofReal)) i k * x k).re = ∑ k, M i k * (x k).re
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply]
  simp [Complex.mul_re]

/-- Lean implementation helper: imaginary part of a complexified matrix–vector
product. -/
lemma im_map_mulVec (M : Matrix V V ℝ) (x : V → ℂ) (i : V) :
    (((M.map (Complex.ofReal)) *ᵥ x) i).im = (M *ᵥ fun k => (x k).im) i := by
  show (∑ k, (M.map (Complex.ofReal)) i k * x k).im = ∑ k, M i k * (x k).im
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply]
  simp [Complex.mul_im]

end ComplexificationBridge

section GraphLaplacian

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Book §5.3.1** (C5-12): the (combinatorial) graph Laplacian
`Δ = D − A`, read in `𝕄_n(ℂ)` as the book does.  Mathlib's
`SimpleGraph.lapMatrix` is literally `degMatrix − adjMatrix`, matching the
book's definition verbatim; we complexify it entrywise.  Explicit source
declaration. -/
noncomputable def lapMatrixC : Matrix V V ℂ :=
  (G.lapMatrix ℝ).map (Complex.ofReal)

/-- **Book §5.3.1** (C5-12): "each Laplacian matrix is positive semidefinite."
Explicit source claim; proved from Mathlib's real statement. -/
lemma posSemidef_lapMatrixC : (lapMatrixC G).PosSemidef :=
  posSemidef_map_ofReal (SimpleGraph.posSemidef_lapMatrix ℝ G)

/-- Lean implementation helper: the complex Laplacian is Hermitian. -/
lemma isHermitian_lapMatrixC : (lapMatrixC G).IsHermitian :=
  (posSemidef_lapMatrixC G).1

/-- **Book §5.3.1** (C5-12): "the vector `e` of ones is always an eigenvector
of `Δ` with eigenvalue zero."  Explicit source claim. -/
lemma lapMatrixC_mulVec_one_eq_zero :
    lapMatrixC G *ᵥ (fun _ => (1 : ℂ)) = 0 := by
  have h := map_mulVec_ofReal (G.lapMatrix ℝ) (fun _ => 1)
  rw [show (fun i : V => (((fun _ : V => (1 : ℝ)) i : ℝ) : ℂ)) =
    (fun _ : V => (1 : ℂ)) from funext fun i => by norm_num] at h
  rw [lapMatrixC, h, SimpleGraph.lapMatrix_mulVec_const_eq_zero]
  funext i
  norm_num

/-- **Book §5.3.1** (C5-12): the normalized Laplacian
`H = D^{−1/2} Δ D^{−1/2}`, "where we place the convention that `0^{−1/2} = 0`
in case a vertex has degree zero."  The convention is automatic for
`Real.rpow` (`0 ^ (−1/2) = 0`).  The book states no results about `H`, so
this is a definition only.  Explicit source declaration. -/
noncomputable def normalizedLapMatrix : Matrix V V ℂ :=
  Matrix.diagonal (fun v => ((((G.degree v : ℝ)) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)) *
    lapMatrixC G *
      Matrix.diagonal
        (fun v => ((((G.degree v : ℝ)) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ))

/-- Lean implementation helper: kernel description of the complex Laplacian in
terms of the real one. -/
lemma lapMatrixC_mulVec_eq_zero_iff {x : V → ℂ} :
    lapMatrixC G *ᵥ x = 0 ↔
      G.lapMatrix ℝ *ᵥ (fun i => (x i).re) = 0 ∧
        G.lapMatrix ℝ *ᵥ (fun i => (x i).im) = 0 := by
  constructor
  · intro h
    constructor
    · funext i
      have hi := congrFun h i
      rw [Pi.zero_apply] at hi
      have h1 := re_map_mulVec (G.lapMatrix ℝ) x i
      rw [show ((G.lapMatrix ℝ).map (Complex.ofReal)) *ᵥ x =
        lapMatrixC G *ᵥ x from rfl, hi] at h1
      rw [Pi.zero_apply, ← h1, Complex.zero_re]
    · funext i
      have hi := congrFun h i
      rw [Pi.zero_apply] at hi
      have h1 := im_map_mulVec (G.lapMatrix ℝ) x i
      rw [show ((G.lapMatrix ℝ).map (Complex.ofReal)) *ᵥ x =
        lapMatrixC G *ᵥ x from rfl, hi] at h1
      rw [Pi.zero_apply, ← h1, Complex.zero_im]
  · rintro ⟨ha, hb⟩
    funext i
    have h1 := re_map_mulVec (G.lapMatrix ℝ) x i
    have h2 := im_map_mulVec (G.lapMatrix ℝ) x i
    rw [ha] at h1
    rw [hb] at h2
    rw [Pi.zero_apply] at h1 h2
    rw [Pi.zero_apply]
    apply Complex.ext
    · rw [Complex.zero_re]
      exact h1
    · rw [Complex.zero_im]
      exact h2

end GraphLaplacian

section Connectivity

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Book §5.3.1** (C5-13): "the graph `G` is connected if and only if the
second-smallest eigenvalue of `Δ` is strictly positive."  Explicit prose claim
(the book cites [GR01]). -/
theorem connected_iff_secondSmallest_pos (hcard : 1 < Fintype.card V) :
    G.Connected ↔
      0 < secondSmallestEigenvalue (isHermitian_lapMatrixC G) := by
  classical
  haveI hNV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  haveI hNW : Nonempty (Fin (Fintype.card V - 1)) := ⟨⟨0, by omega⟩⟩
  have hn0 : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  -- the unit vector `e/√n` and the compression isometry
  set v : V → ℂ := fun _ => (((Real.sqrt (Fintype.card V))⁻¹ : ℝ) : ℂ)
    with hvdef
  have hsq : Real.sqrt (Fintype.card V) ^ 2 = (Fintype.card V : ℝ) :=
    Real.sq_sqrt (le_of_lt hn0)
  have hsqpos : 0 < Real.sqrt (Fintype.card V) := Real.sqrt_pos.mpr hn0
  have hv : l2norm v = 1 := by
    have h1 : l2norm v ^ 2 = 1 := by
      rw [l2norm_sq]
      have h2 : ∀ i : V, ‖v i‖ ^ 2 = ((Real.sqrt (Fintype.card V))⁻¹) ^ 2 :=
        fun i => by
          rw [hvdef]
          show ‖(((Real.sqrt (Fintype.card V))⁻¹ : ℝ) : ℂ)‖ ^ 2 = _
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, inv_pow, hsq,
        mul_inv_cancel₀ (ne_of_gt hn0)]
    have h3 : (l2norm v - 1) * (l2norm v + 1) = 0 := by nlinarith [h1]
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · linarith [l2norm_nonneg v]
  obtain ⟨R, hRR, hRv⟩ := exists_compression_isometry (v := v) hv
  have hcard' : Fintype.card (Fin (Fintype.card V - 1)) + 1 =
      Fintype.card V := by
    rw [Fintype.card_fin]; omega
  have hvsmul : v = (((Real.sqrt (Fintype.card V))⁻¹ : ℝ) : ℂ) •
      (fun _ : V => (1 : ℂ)) := by
    rw [hvdef]
    funext i
    show (((Real.sqrt (Fintype.card V))⁻¹ : ℝ) : ℂ) =
      (((Real.sqrt (Fintype.card V))⁻¹ : ℝ) : ℂ) • (1 : ℂ)
    rw [smul_eq_mul, mul_one]
  have hΔv : lapMatrixC G *ᵥ v = 0 := by
    rw [hvsmul, Matrix.mulVec_smul, lapMatrixC_mulVec_one_eq_zero, smul_zero]
  have hpsd := posSemidef_lapMatrixC G
  have hC : (R * lapMatrixC G * Rᴴ).PosSemidef :=
    hpsd.mul_mul_conjTranspose_same R
  have hid : lambdaMin hC.1 =
      secondSmallestEigenvalue (isHermitian_lapMatrixC G) :=
    lambdaMin_compression_eq_secondSmallest hpsd hv hΔv hRR hRv hcard' hC.1
  constructor
  · -- connected ⟹ λ₂↑ > 0
    intro hconn
    rw [← hid]
    rcases (le_lambdaMin hC.1 fun i => hC.eigenvalues_nonneg i).lt_or_eq
      with hlt | heq
    · exact hlt
    exfalso
    -- a unit vector attaining λ_min = 0 yields a kernel vector of `Δ`
    obtain ⟨u, hu, hru⟩ := exists_unit_rayleigh_eq_lambdaMin hC.1
    have hquad : star u ⬝ᵥ ((R * lapMatrixC G * Rᴴ) *ᵥ u) = 0 := by
      rw [star_dotProduct_mulVec_eq_rayleigh hC.1, hru, ← heq]
      norm_num
    have hCu : (R * lapMatrixC G * Rᴴ) *ᵥ u = 0 :=
      mulVec_eq_zero_of_dotProduct_eq_zero hC hquad
    set y : V → ℂ := Rᴴ *ᵥ u with hydef
    have hyΔy : star y ⬝ᵥ (lapMatrixC G *ᵥ y) = 0 := by
      rw [hydef, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
        Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        show R * (lapMatrixC G * Rᴴ) = R * lapMatrixC G * Rᴴ from
          (Matrix.mul_assoc _ _ _).symm,
        ← Matrix.dotProduct_mulVec, hCu, dotProduct_zero]
    have hΔy : lapMatrixC G *ᵥ y = 0 :=
      mulVec_eq_zero_of_dotProduct_eq_zero hpsd hyΔy
    obtain ⟨hre, him⟩ := (lapMatrixC_mulVec_eq_zero_iff G).mp hΔy
    have hconst : ∀ i j : V, y i = y j := fun i j => by
      apply Complex.ext
      · exact (SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable
          (G := G)).mp hre i j (hconn.preconnected i j)
      · exact (SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable
          (G := G)).mp him i j (hconn.preconnected i j)
    -- `y ⟂ v`
    have hyv : star v ⬝ᵥ y = 0 := by
      rw [hydef, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hRv]
      simp
    -- `y` constant and `y ⟂ v` force `y = 0`
    set c : ℂ := y (Classical.arbitrary V) with hcdef
    have hsum : star v ⬝ᵥ y =
        (((Real.sqrt (Fintype.card V))⁻¹ : ℝ) : ℂ) * (Fintype.card V : ℂ) *
          c := by
      calc star v ⬝ᵥ y
          = ∑ i : V, (((Real.sqrt (Fintype.card V))⁻¹ : ℝ) : ℂ) * c := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Pi.star_apply, hvdef]
            show star (((Real.sqrt (Fintype.card V))⁻¹ : ℝ) : ℂ) * y i = _
            rw [Complex.star_def, Complex.conj_ofReal, hconst i
              (Classical.arbitrary V), ← hcdef]
        _ = (Fintype.card V : ℂ) *
            ((((Real.sqrt (Fintype.card V))⁻¹ : ℝ) : ℂ) * c) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = _ := by ring
    have hc0 : c = 0 := by
      rw [hyv] at hsum
      have hne1 : ((((Real.sqrt (Fintype.card V))⁻¹ : ℝ)) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact inv_ne_zero (ne_of_gt hsqpos)
      have hne2 : ((Fintype.card V : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact ne_of_gt hn0
      have h4 : ((Fintype.card V : ℝ) : ℂ) = (Fintype.card V : ℂ) := by
        push_cast
        rfl
      rcases mul_eq_zero.mp hsum.symm with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hne1
        · exact absurd h' (h4 ▸ hne2)
      · exact h
    have hy0 : y = 0 := by
      funext i
      rw [Pi.zero_apply, hconst i (Classical.arbitrary V), ← hcdef, hc0]
    -- yet `‖y‖ = 1`
    have hynorm : star y ⬝ᵥ y = 1 := by
      rw [hydef, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
        Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hRR,
        Matrix.vecMul_one, dotProduct_star_self_eq, hu]
      norm_num
    rw [hy0] at hynorm
    simp at hynorm
  · -- λ₂↑ > 0 ⟹ connected
    intro hpos
    by_contra hnc
    rw [SimpleGraph.connected_iff] at hnc
    push Not at hnc
    have hnp : ¬ G.Preconnected := fun hp => (hnc hp).elim (Classical.arbitrary V)
    unfold SimpleGraph.Preconnected at hnp
    push Not at hnp
    obtain ⟨s, t, hst⟩ := hnp
    -- the indicator of the reachability class of `s` lies in the kernel
    set x : V → ℝ := fun i => if G.Reachable s i then 1 else 0 with hxdef
    have hx0 : G.lapMatrix ℝ *ᵥ x = 0 := by
      rw [SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable]
      intro i j hij
      by_cases hsi : G.Reachable s i
      · rw [hxdef]
        simp [hsi, hsi.trans hij]
      · have hsj : ¬ G.Reachable s j := fun h => hsi (h.trans hij.symm)
        rw [hxdef]
        simp [hsi, hsj]
    set z : V → ℂ := fun i => ((x i : ℝ) : ℂ) with hzdef
    have hz0 : lapMatrixC G *ᵥ z = 0 := by
      rw [lapMatrixC_mulVec_eq_zero_iff]
      constructor
      · rw [show (fun i => (z i).re) = x from funext fun i => by
          rw [hzdef]; exact Complex.ofReal_re _]
        exact hx0
      · rw [show (fun i => (z i).im) = (0 : V → ℝ) from funext fun i => by
          rw [hzdef]; exact Complex.ofReal_im _]
        rw [Matrix.mulVec_zero]
    -- project out the `v`-component
    set c : ℂ := star v ⬝ᵥ z with hcdef
    set w : V → ℂ := z - c • v with hwdef
    have hw0 : lapMatrixC G *ᵥ w = 0 := by
      rw [hwdef, Matrix.mulVec_sub, Matrix.mulVec_smul, hz0, hΔv, smul_zero,
        sub_zero]
    have hwv : star v ⬝ᵥ w = 0 := by
      rw [hwdef, dotProduct_sub, dotProduct_smul, dotProduct_star_self_eq, hv,
        ← hcdef]
      simp
    have hwne : w ≠ 0 := by
      intro h
      have hz : z = c • v := by rwa [hwdef, sub_eq_zero] at h
      have h1 : z s = z t := by
        rw [hz]
        show c * v s = c * v t
        rw [hvdef]
      rw [hzdef] at h1
      have hxs : x s = 1 := by rw [hxdef]; simp
      have hxt : x t = 0 := by rw [hxdef]; simp [hst]
      rw [show ((fun i => ((x i : ℝ) : ℂ)) s) = ((x s : ℝ) : ℂ) from rfl,
        show ((fun i => ((x i : ℝ) : ℂ)) t) = ((x t : ℝ) : ℂ) from rfl,
        hxs, hxt] at h1
      norm_num at h1
    -- push through the isometry: `u = Rw` is a kernel vector of `RΔR*`
    have hRtR := conjTranspose_mul_self_eq_one_sub hv hRR hRv hcard'
    set uu : Fin (Fintype.card V - 1) → ℂ := R *ᵥ w with huudef
    have hRtRw : Rᴴ *ᵥ uu = w := by
      rw [huudef, Matrix.mulVec_mulVec, hRtR, Matrix.sub_mulVec,
        Matrix.one_mulVec]
      have h1 : (Matrix.of fun i j => v i * star (v j)) *ᵥ w =
          fun i => v i * (star v ⬝ᵥ w) := by
        funext i
        show ∑ j, (Matrix.of fun i j => v i * star (v j)) i j * w j = _
        rw [show star v ⬝ᵥ w = ∑ j, star (v j) * w j from rfl,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.of_apply, mul_assoc]
      rw [h1, hwv]
      funext i
      rw [Pi.sub_apply]
      show w i - v i * 0 = w i
      ring
    have huune : uu ≠ 0 := fun h =>
      hwne (by rw [← hRtRw, h, Matrix.mulVec_zero])
    have hCu : (R * lapMatrixC G * Rᴴ) *ᵥ uu = 0 := by
      rw [show R * lapMatrixC G * Rᴴ = R * lapMatrixC G * Rᴴ from rfl,
        ← Matrix.mulVec_mulVec, hRtRw, ← Matrix.mulVec_mulVec, hw0,
        Matrix.mulVec_zero]
    -- Rayleigh value 0 at a nonzero vector forces `λ_min ≤ 0`
    have hray : rayleigh (R * lapMatrixC G * Rᴴ) uu = 0 := by
      rw [rayleigh, hCu, dotProduct_zero, Complex.zero_re]
    have hle := lambdaMin_le_rayleigh hC.1 uu
    rw [hray] at hle
    have hnormpos : 0 < l2norm uu := by
      rcases (l2norm_nonneg uu).lt_or_eq with h | h
      · exact h
      exfalso
      apply huune
      have hsum0 : ∑ i, ‖uu i‖ ^ 2 = 0 := by
        rw [← l2norm_sq, ← h]
        norm_num
      funext i
      have h5 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => by positivity)).mp hsum0 i (Finset.mem_univ i)
      rw [Pi.zero_apply, ← norm_eq_zero]
      nlinarith [norm_nonneg (uu i)]
    have hmin_le : lambdaMin hC.1 ≤ 0 := by
      have h6 : 0 < l2norm uu ^ 2 := pow_pos hnormpos 2
      nlinarith
    rw [hid] at hmin_le
    linarith

end Connectivity

end MatrixConcentration

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Application: connectivity of an Erdős–Rényi graph (Tropp §5.3.2–§5.3.3)

* `laplCoeff` — the Laplacian summand `E_jj + E_kk − E_jk − E_kj` of the
  representation **Book (5.3.3)**, realized as the outer
  product `(e_j − e_k)(e_j − e_k)*`, with `laplCoeff_eq_singles` recovering the
  displayed four-term form;
* `erLaplacian` — the random Laplacian `Δ = Σ_{j<k} ξ_jk·(E_jj+E_kk−E_jk−E_kj)`;
  the adjacency representation **Book (5.3.2)** is
  `erAdjacency` (`= Σ ξ_jk·(E_jk+E_kj)`, i.e. the Chapter-4 `wignerCoeff`
  family);
* `laplCoeff_sq` — the §5.3.3 computation `T² = 2T` (C5-16), and
  `compressed_summand_bounds` — `0 ≤ λ_min`, `λ_max ≤ 2` for the compressed
  summands (`L = 2`);
* `sum_laplCoeff` — `Σ_{j<k} T_p = n·I − ee*` (the §5.3.3 display), and
  `expectation_erY_eq` — `𝔼Y = pn·I` (C5-17);
* `er_compression_tail` — the §5.3.3 display
  `P(λ_min(Y) ≤ t·pn) ≤ (n−1)·[e^{t−1}/t^t]^{pn/2}` for `t ∈ (0,1)` (C5-18);
* `er_second_smallest_tail` — the same bound for `λ₂↑(Δ)`, via the
  Courant–Fischer identification of `07_Compression`.

-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable [IsProbabilityMeasure μ]

section LaplacianCoefficients

variable {d : ℕ}

/-- Lean implementation helper: the edge difference vector `e_j − e_k`. -/
noncomputable def diffVec (p : WignerIndex d) : Fin d → ℂ :=
  Pi.single p.1.1 1 - Pi.single p.1.2 1

/-- Lean implementation helper: coordinate formula for the edge difference vector. -/
lemma diffVec_apply (p : WignerIndex d) (x : Fin d) :
    diffVec p x = (if x = p.1.1 then 1 else 0) - (if x = p.1.2 then 1 else 0) := by
  show ((Pi.single p.1.1 1 - Pi.single p.1.2 1 : Fin d → ℂ)) x = _
  rw [Pi.sub_apply, Pi.single_apply, Pi.single_apply]

/-- **Book (5.3.3)** summand (C5-14): the Laplacian coefficient
`E_jj + E_kk − E_jk − E_kj`, realized as the outer product
`(e_j − e_k)(e_j − e_k)*`.  Explicit source declaration. -/
noncomputable def laplCoeff (p : WignerIndex d) : Matrix (Fin d) (Fin d) ℂ :=
  colVec (diffVec p) * rowVec (star (diffVec p))

/-- Lean implementation helper: entrywise outer-product formula for a Laplacian coefficient. -/
lemma laplCoeff_apply (p : WignerIndex d) (a b : Fin d) :
    laplCoeff p a b = diffVec p a * star (diffVec p b) := by
  rw [laplCoeff, Matrix.mul_apply]
  rw [Fintype.sum_unique fun u : Unit =>
    colVec (diffVec p) a u * rowVec (star (diffVec p)) u b]
  rfl

/-- **Book (5.3.3)**: the displayed four-term form
`E_jj + E_kk − E_jk − E_kj` of the Laplacian summand. -/
lemma laplCoeff_eq_singles (p : WignerIndex d) :
    laplCoeff p = Matrix.single p.1.1 p.1.1 1 + Matrix.single p.1.2 p.1.2 1 -
      Matrix.single p.1.1 p.1.2 1 - Matrix.single p.1.2 p.1.1 1 := by
  obtain ⟨⟨j, k⟩, hjk⟩ := p
  have hne : j ≠ k := ne_of_lt hjk
  have hne' : k ≠ j := Ne.symm hne
  ext a b
  rw [laplCoeff_apply, diffVec_apply, diffVec_apply]
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.single_apply, Matrix.single_apply, Matrix.single_apply,
    Matrix.single_apply]
  show ((if a = j then (1:ℂ) else 0) - (if a = k then 1 else 0)) *
      star ((if b = j then (1:ℂ) else 0) - (if b = k then 1 else 0)) = _
  rw [star_sub]
  rw [show star (if b = j then (1:ℂ) else 0) = (if b = j then 1 else 0) from by
    split_ifs <;> simp]
  rw [show star (if b = k then (1:ℂ) else 0) = (if b = k then 1 else 0) from by
    split_ifs <;> simp]
  by_cases haj : a = j <;> by_cases hak : a = k <;>
    by_cases hbj : b = j <;> by_cases hbk : b = k
  · exact absurd (haj ▸ hak ▸ rfl : j = k) (by simp_all)
  all_goals simp_all [eq_comm]

/-- Lean implementation helper: `‖e_j − e_k‖² = 2`. -/
lemma l2norm_sq_diffVec (p : WignerIndex d) : l2norm (diffVec p) ^ 2 = 2 := by
  obtain ⟨⟨j, k⟩, hjk⟩ := p
  have hne : j ≠ k := ne_of_lt hjk
  rw [l2norm_sq]
  have hterm : ∀ i : Fin d, ‖diffVec ⟨(j, k), hjk⟩ i‖ ^ 2 =
      (if i = j then (1 : ℝ) else 0) + (if i = k then 1 else 0) := by
    intro i
    rw [diffVec_apply]
    by_cases hij : i = j <;> by_cases hik : i = k
    · exact absurd (hij ▸ hik ▸ rfl : j = k) (by simp_all)
    all_goals simp_all
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ j (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' Finset.univ k (fun _ => (1 : ℝ))]
  norm_num

/-- Lean implementation helper: the Laplacian summand is psd (the "Conjugation
Rule" remark of §5.3.3 applied to the outer-product form). -/
lemma posSemidef_laplCoeff (p : WignerIndex d) : (laplCoeff p).PosSemidef := by
  rw [laplCoeff, show rowVec (star (diffVec p)) = (colVec (diffVec p))ᴴ from by
    ext u x
    rfl]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- **Book §5.3.3 (C5-16)**: `T² = 2T` for the Laplacian summand — "a direct
calculation shows that `T = E_jj + E_kk − E_jk − E_kj` satisfies the polynomial
`T² = 2T`, so each eigenvalue of `T` must equal zero or two."  Explicit source
declaration. -/
lemma laplCoeff_sq (p : WignerIndex d) :
    laplCoeff p * laplCoeff p = (2 : ℂ) • laplCoeff p := by
  have h1 : rowVec (star (diffVec p)) * colVec (diffVec p) =
      (2 : ℂ) • (1 : Matrix Unit Unit ℂ) := by
    rw [rowVec_mul_colVec]
    ext u u'
    rw [Matrix.of_apply, dotProduct_star_self_eq, l2norm_sq_diffVec,
      Matrix.smul_apply, Matrix.one_apply_eq]
    norm_num
  calc laplCoeff p * laplCoeff p
      = colVec (diffVec p) * ((rowVec (star (diffVec p)) * colVec (diffVec p)) *
          rowVec (star (diffVec p))) := by
        rw [laplCoeff, Matrix.mul_assoc]
        congr 1
        exact (Matrix.mul_assoc _ _ _).symm
  _ = colVec (diffVec p) * ((2 : ℂ) • (1 : Matrix Unit Unit ℂ) *
        rowVec (star (diffVec p))) := by rw [h1]
  _ = (2 : ℂ) • laplCoeff p := by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, laplCoeff]

/-- Lean implementation helper: `‖T‖ ≤ 2` (the §5.3.3 norm computation, via the
outer-product bound). -/
lemma l2_opNorm_laplCoeff_le (p : WignerIndex d) : ‖laplCoeff p‖ ≤ 2 := by
  refine l2_opNorm_le_of_forall_dotProduct _ (by norm_num) fun u w => ?_
  have hMw : (laplCoeff p) *ᵥ w = fun i => diffVec p i * (star (diffVec p) ⬝ᵥ w) := by
    funext i
    show ∑ j, laplCoeff p i j * w j = _
    rw [show (∑ j, laplCoeff p i j * w j) =
      ∑ j, diffVec p i * (star (diffVec p j) * w j) from
      Finset.sum_congr rfl fun j _ => by
        rw [laplCoeff_apply]
        ring]
    rw [← Finset.mul_sum]
    rfl
  rw [hMw]
  have hdot : star u ⬝ᵥ (fun i => diffVec p i * (star (diffVec p) ⬝ᵥ w)) =
      (star u ⬝ᵥ diffVec p) * (star (diffVec p) ⬝ᵥ w) := by
    show (∑ i, star (u i) * (diffVec p i * (star (diffVec p) ⬝ᵥ w))) = _
    rw [show (∑ i, star (u i) * (diffVec p i * (star (diffVec p) ⬝ᵥ w))) =
      (∑ i, star (u i) * diffVec p i) * (star (diffVec p) ⬝ᵥ w) from by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring]
    rfl
  rw [hdot, norm_mul]
  have h1 := norm_dotProduct_le u (diffVec p)
  have h2 := norm_dotProduct_le (diffVec p) w
  have hv2 : l2norm (diffVec p) ^ 2 = 2 := l2norm_sq_diffVec p
  calc ‖star u ⬝ᵥ diffVec p‖ * ‖star (diffVec p) ⬝ᵥ w‖
      ≤ (l2norm u * l2norm (diffVec p)) * (l2norm (diffVec p) * l2norm w) :=
        mul_le_mul h1 h2 (norm_nonneg _)
          (mul_nonneg (l2norm_nonneg _) (l2norm_nonneg _))
  _ = 2 * l2norm u * l2norm w := by
      rw [show (l2norm u * l2norm (diffVec p)) * (l2norm (diffVec p) * l2norm w) =
        l2norm (diffVec p) ^ 2 * l2norm u * l2norm w from by ring, hv2]

end LaplacianCoefficients

section ErdosRenyiModel

variable {d : ℕ}

/-- **Book (5.3.2)** (C5-14): the adjacency matrix of a
random graph in `G(n,p)`, `A = Σ_{j<k} ξ_jk (E_jk + E_kj)` (the coefficient
family is the Chapter-4 `wignerCoeff`).  Explicit source declaration. -/
noncomputable def erAdjacency (ξ : WignerIndex d → Ω → ℝ) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ p, ξ p ω • wignerCoeff p

/-- **Book (5.3.3)** (C5-14): the Laplacian of the
random graph, `Δ = Σ_{j<k} ξ_jk (E_jj + E_kk − E_jk − E_kj)`.  Explicit source
declaration. -/
noncomputable def erLaplacian (ξ : WignerIndex d → Ω → ℝ) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ p, ξ p ω • laplCoeff p

/-- Lean implementation helper: `Σ_{j<k} (E_jk + E_kj) = ee* − I`. -/
lemma sum_wignerCoeff (d : ℕ) :
    (∑ p : WignerIndex d, wignerCoeff p) =
      Matrix.of (fun _ _ => (1 : ℂ)) - 1 := by
  classical
  ext a b
  rw [Matrix.sum_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply]
  have h0 : (∑ p : WignerIndex d, wignerCoeff p a b) =
      ∑ q ∈ Finset.univ.filter (fun q : Fin d × Fin d => q.1 < q.2),
        (Matrix.single q.1 q.2 (1:ℂ) a b + Matrix.single q.2 q.1 1 a b) :=
    (Finset.sum_subtype (p := fun q : Fin d × Fin d => q.1 < q.2)
      (Finset.univ.filter fun q : Fin d × Fin d => q.1 < q.2)
      (fun q => by simp)
      (fun q => Matrix.single q.1 q.2 (1:ℂ) a b +
        Matrix.single q.2 q.1 1 a b)).symm
  rw [h0, Finset.sum_add_distrib]
  have h1 : (∑ q ∈ Finset.univ.filter (fun q : Fin d × Fin d => q.1 < q.2),
      Matrix.single q.1 q.2 (1:ℂ) a b) = if a < b then 1 else 0 := by
    rw [Finset.sum_congr rfl fun q _ => show Matrix.single q.1 q.2 (1:ℂ) a b =
      if q = (a, b) then 1 else 0 from by
        rw [Matrix.single_apply]
        exact if_congr (by rw [Prod.ext_iff]) rfl rfl]
    rw [Finset.sum_ite_eq' (Finset.univ.filter fun q : Fin d × Fin d =>
      q.1 < q.2) (a, b) (fun _ => (1:ℂ))]
    simp
  have h2 : (∑ q ∈ Finset.univ.filter (fun q : Fin d × Fin d => q.1 < q.2),
      Matrix.single q.2 q.1 (1:ℂ) a b) = if b < a then 1 else 0 := by
    rw [Finset.sum_congr rfl fun q _ => show Matrix.single q.2 q.1 (1:ℂ) a b =
      if q = (b, a) then 1 else 0 from by
        rw [Matrix.single_apply]
        exact if_congr (by rw [Prod.ext_iff]; tauto) rfl rfl]
    rw [Finset.sum_ite_eq' (Finset.univ.filter fun q : Fin d × Fin d =>
      q.1 < q.2) (b, a) (fun _ => (1:ℂ))]
    simp
  rw [h1, h2]
  rcases lt_trichotomy a b with h | h | h
  · rw [if_pos h, if_neg (not_lt_of_gt h), if_neg (ne_of_lt h)]
    ring
  · subst h
    simp
  · rw [if_neg (not_lt_of_gt h), if_pos h, if_neg (Ne.symm (ne_of_lt h))]
    ring

/-- **Book §5.3.3 display** (C5-17, first identity):
`Σ_{j<k} (E_jj + E_kk − E_jk − E_kj) = (n−1)·I − (ee* − I) = n·I − ee*`.
Explicit source declaration. -/
theorem sum_laplCoeff (d : ℕ) :
    (∑ p : WignerIndex d, laplCoeff p) =
      (d : ℂ) • 1 - Matrix.of (fun _ _ => (1 : ℂ)) := by
  classical
  have h1 : (fun p : WignerIndex d => laplCoeff p) = fun p =>
      (wignerCoeff p) ^ 2 - wignerCoeff p := by
    funext p
    rw [laplCoeff_eq_singles p, wignerCoeff_sq p, wignerCoeff]
    abel
  rw [show (∑ p : WignerIndex d, laplCoeff p) =
    ∑ p : WignerIndex d, ((wignerCoeff p) ^ 2 - wignerCoeff p) from by
      rw [← h1]]
  rw [Finset.sum_sub_distrib, wigner_coeff_sq_sum, sum_wignerCoeff]
  rw [sub_smul, one_smul]
  abel

/-- Lean implementation helper: `T_p *ᵥ x = ((e_j−e_k)* x)·(e_j−e_k)`. -/
lemma laplCoeff_mulVec (p : WignerIndex d) (x : Fin d → ℂ) :
    laplCoeff p *ᵥ x = fun i => diffVec p i * (star (diffVec p) ⬝ᵥ x) := by
  funext i
  show ∑ j, laplCoeff p i j * x j = _
  rw [show (∑ j, laplCoeff p i j * x j) =
    ∑ j, diffVec p i * (star (diffVec p j) * x j) from
    Finset.sum_congr rfl fun j _ => by
      rw [laplCoeff_apply]
      ring]
  rw [← Finset.mul_sum]
  rfl

/-- Lean implementation helper: the ones vector annihilates each summand. -/
lemma laplCoeff_mulVec_one (p : WignerIndex d) :
    laplCoeff p *ᵥ (fun _ => (1 : ℂ)) = 0 := by
  rw [laplCoeff_mulVec]
  funext i
  have h1 : star (diffVec p) ⬝ᵥ (fun _ => (1 : ℂ)) = 0 := by
    show (∑ j, star (diffVec p j) * 1) = 0
    rw [show (∑ j, star (diffVec p j) * 1) = star (∑ j, diffVec p j) from by
      rw [star_sum]
      exact Finset.sum_congr rfl fun j _ => (mul_one _)]
    rw [show (∑ j, diffVec p j) = 0 from ?_, star_zero]
    rw [show (∑ j, diffVec p j) = ∑ j, ((if j = p.1.1 then 1 else 0) -
      (if j = p.1.2 then (1:ℂ) else 0)) from
      Finset.sum_congr rfl fun j _ => diffVec_apply p j]
    rw [Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ p.1.1 (fun _ => (1:ℂ)),
      Finset.sum_ite_eq' Finset.univ p.1.2 (fun _ => (1:ℂ))]
    simp
  rw [h1, mul_zero]
  rfl

/-- **Book §5.3.1** ("the smallest eigenvalue of `Δ` has eigenvector `e`"):
`Δ·e = 0` for the random Laplacian.  Implicit source declaration. -/
lemma erLaplacian_mulVec_one (ξ : WignerIndex d → Ω → ℝ) (ω : Ω) :
    erLaplacian ξ ω *ᵥ (fun _ => (1 : ℂ)) = 0 := by
  rw [erLaplacian, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Matrix.smul_mulVec, laplCoeff_mulVec_one, smul_zero]

/-- Lean implementation helper: the random Laplacian is psd. -/
lemma posSemidef_erLaplacian {ξ : WignerIndex d → Ω → ℝ}
    (hrange : ∀ p ω, ξ p ω = 0 ∨ ξ p ω = 1) (ω : Ω) :
    (erLaplacian ξ ω).PosSemidef := by
  refine posSemidef_matsum Finset.univ fun p => ?_
  rcases hrange p ω with h | h <;> rw [h]
  · rw [zero_smul]
    exact Matrix.PosSemidef.zero
  · rw [one_smul]
    exact posSemidef_laplCoeff p

end ErdosRenyiModel

section CompressionTail

variable {d : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
variable {ξ : WignerIndex d → Ω → ℝ} {R : Matrix W (Fin d) ℂ}

/-- Lean implementation helper: `λ_min(I) = 1`. -/
lemma lambdaMin_one {V' : Type*} [Fintype V'] [DecidableEq V'] [Nonempty V'] :
    lambdaMin (Matrix.isHermitian_one (n := V') (α := ℂ)) = 1 := by
  obtain ⟨u, hu, hval⟩ := exists_unit_rayleigh_eq_lambdaMin
    (Matrix.isHermitian_one (n := V') (α := ℂ))
  rw [← hval]
  show ((star u) ⬝ᵥ ((1 : Matrix V' V' ℂ) *ᵥ u)).re = 1
  rw [Matrix.one_mulVec, dotProduct_star_self_eq, hu]
  norm_num

/-- **Book (5.3.5)** (C5-15): the compressed random matrix
`Y = RΔR* = Σ_{j<k} ξ_jk·R(E_jj+E_kk−E_jk−E_kj)R*`.  Explicit source
declaration (the second equality). -/
lemma compressed_sum_eq (ξ : WignerIndex d → Ω → ℝ) (R : Matrix W (Fin d) ℂ)
    (ω : Ω) :
    (∑ p, ξ p ω • (R * laplCoeff p * Rᴴ)) = R * erLaplacian ξ ω * Rᴴ := by
  rw [erLaplacian, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Lean implementation helper: the compressed summands are Hermitian. -/
lemma isHermitian_compressed (p : WignerIndex d) (R : Matrix W (Fin d) ℂ)
    (c : ℝ) : (c • (R * laplCoeff p * Rᴴ)).IsHermitian :=
  isHermitian_real_smul
    ((posSemidef_laplCoeff p).mul_mul_conjTranspose_same R).1 _

/-- **Book §5.3.3 (C5-16)**: the eigenvalue bounds for the compressed summands —
`0 ≤ λ_min` and `λ_max ≤ L = 2` ("we show that `L = 2` is an upper bound for the
eigenvalues of each summand", via submultiplicativity, `‖R‖ = 1`, and
`T² = 2T`).  Explicit source declaration. -/
lemma compressed_summand_bounds [Nonempty W]
    (hrange : ∀ p ω, ξ p ω = 0 ∨ ξ p ω = 1) (hRR : R * Rᴴ = 1)
    (hherm : ∀ (p : WignerIndex d) ω,
      ((fun p ω => ξ p ω • (R * laplCoeff p * Rᴴ)) p ω).IsHermitian) :
    (∀ p ω, 0 ≤ lambdaMin (hherm p ω)) ∧
      (∀ p ω, lambdaMax (hherm p ω) ≤ 2) := by
  have hnormR : ‖R‖ = 1 := by
    have h1 : ‖R‖ ^ 2 = ‖R * Rᴴ‖ := (l2_opNorm_sq_eq R).1
    rw [hRR, l2_opNorm_one] at h1
    nlinarith [norm_nonneg R]
  have hpsd : ∀ (p : WignerIndex d) ω, (ξ p ω • (R * laplCoeff p * Rᴴ)).PosSemidef := by
    intro p ω
    rcases hrange p ω with h | h <;> rw [h]
    · rw [zero_smul]
      exact Matrix.PosSemidef.zero
    · rw [one_smul]
      exact (posSemidef_laplCoeff p).mul_mul_conjTranspose_same R
  constructor
  · intro p ω
    exact le_lambdaMin _ fun i => (hpsd p ω).eigenvalues_nonneg i
  · intro p ω
    have h1 : lambdaMax (hherm p ω) ≤ ‖ξ p ω • (R * laplCoeff p * Rᴴ)‖ :=
      (le_abs_self _).trans (abs_lambdaMax_le _)
    refine h1.trans ?_
    have h2 : ‖ξ p ω • (R * laplCoeff p * Rᴴ)‖ ≤ ‖R * laplCoeff p * Rᴴ‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      rcases hrange p ω with h | h <;> rw [h]
      · simp [norm_nonneg]
      · simp
    refine h2.trans ?_
    calc ‖R * laplCoeff p * Rᴴ‖
        ≤ ‖R * laplCoeff p‖ * ‖Rᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖R‖ * ‖laplCoeff p‖ * ‖Rᴴ‖ := by
        refine mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ 2 := by
        rw [Matrix.l2_opNorm_conjTranspose, hnormR]
        have := l2_opNorm_laplCoeff_le p
        nlinarith [norm_nonneg (laplCoeff p)]

/-- **Book §5.3.3 displays** (C5-17): `𝔼Y = pn·I` — "The first identity follows
when we apply linearity of expectation … The last identity holds because of the
properties of `R`."  Explicit source declaration. -/
theorem expectation_erY_eq [Nonempty W] {prob : ℝ}
    (hprob : prob ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ p, Measurable (ξ p)) (hlaw : ∀ p, IsBernoulli prob (ξ p) μ)
    (hRR : R * Rᴴ = 1) (hRone : R *ᵥ (fun _ => (1 : ℂ)) = 0) :
    (∑ p : WignerIndex d, expectation μ
        (fun ω => ξ p ω • (R * laplCoeff p * Rᴴ))) =
      (prob * d) • (1 : Matrix W W ℂ) := by
  have h1 : ∀ p : WignerIndex d, expectation μ
      (fun ω => ξ p ω • (R * laplCoeff p * Rᴴ)) =
      prob • (R * laplCoeff p * Rᴴ) := by
    intro p
    ext i j
    rw [expectation_apply, Matrix.smul_apply]
    have h2 : (fun ω => (ξ p ω • (R * laplCoeff p * Rᴴ)) i j) =
        fun ω => ξ p ω • (R * laplCoeff p * Rᴴ) i j := by
      funext ω
      rw [Matrix.smul_apply]
    rw [h2, integral_smul_const, integral_id_isBernoulli hprob (hmeas p) (hlaw p)]
  rw [Finset.sum_congr rfl fun p _ => h1 p, ← Finset.smul_sum]
  have h3 : (∑ p : WignerIndex d, R * laplCoeff p * Rᴴ) =
      R * (∑ p : WignerIndex d, laplCoeff p) * Rᴴ := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
  rw [h3, sum_laplCoeff]
  -- `R(n·I − ee*)R* = n·I`
  have hones : R * Matrix.of (fun _ _ : Fin d => (1 : ℂ)) * Rᴴ = 0 := by
    have h4 : Matrix.of (fun _ _ : Fin d => (1 : ℂ)) =
        colVec (fun _ => 1) * rowVec (fun _ => 1) := by
      ext a b
      rw [Matrix.of_apply, Matrix.mul_apply]
      rw [Fintype.sum_unique fun u : Unit =>
        colVec (fun _ : Fin d => (1:ℂ)) a u * rowVec (fun _ : Fin d => (1:ℂ)) u b]
      show (1 : ℂ) = 1 * 1
      ring
    rw [h4, show R * (colVec (fun _ : Fin d => (1:ℂ)) *
      rowVec (fun _ : Fin d => (1:ℂ))) * Rᴴ =
      (R * colVec (fun _ : Fin d => (1:ℂ))) *
        (rowVec (fun _ : Fin d => (1:ℂ)) * Rᴴ) from by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]]
    rw [mul_colVec, hRone, colVec_zero, Matrix.zero_mul]
  have h5 : R * ((d : ℂ) • 1 - Matrix.of (fun _ _ : Fin d => (1 : ℂ))) * Rᴴ =
      (d : ℂ) • (1 : Matrix W W ℂ) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hRR, hones, sub_zero]
  rw [h5]
  have hcast : ((d : ℂ)) • (1 : Matrix W W ℂ) = ((d : ℝ)) • 1 := by
    rw [real_smul_eq_complex_smul (d : ℝ) (1 : Matrix W W ℂ)]
    norm_num
  rw [hcast, smul_smul]

/-- **Book §5.3.3 final display** (C5-18), compression form:
`P(λ_min(Y) ≤ t·pn) ≤ (n−1)·[e^{t−1}/t^t]^{pn/2}` for `t ∈ [0, 1)`.
Explicit source declaration; instance of the matrix Chernoff lower tail (5.1.5)
at `ε = 1 − t` with `μ_min = pn` and `L = 2`.

**Author note.** This pointwise-support form is retained for compatibility; see
`er_compression_tail_of_isBernoulli` for the source-faithful law-only sibling. -/
theorem er_compression_tail [Nonempty W] {prob : ℝ}
    (hprob : prob ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ p, Measurable (ξ p)) (hlaw : ∀ p, IsBernoulli prob (ξ p) μ)
    (hrange : ∀ p ω, ξ p ω = 0 ∨ ξ p ω = 1)
    (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hRR : R * Rᴴ = 1) (hRone : R *ᵥ (fun _ => (1 : ℂ)) = 0)
    (hherm : ∀ (p : WignerIndex d) ω,
      ((fun p ω => ξ p ω • (R * laplCoeff p * Rᴴ)) p ω).IsHermitian)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    μ.real {ω | lambdaMin (isHermitian_matsum Finset.univ (fun p => hherm p ω)) ≤
        t * (prob * d)} ≤
      (Fintype.card W : ℝ) *
        (Real.exp (t - 1) / t ^ (t : ℝ)) ^ (prob * d / 2) := by
  classical
  obtain ⟨hmin, hmax⟩ := compressed_summand_bounds hrange hRR hherm
  have hXmeas : ∀ p, Measurable
      ((fun p ω => ξ p ω • (R * laplCoeff p * Rᴴ)) p) := fun p => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => ξ p ω • (R * laplCoeff p * Rᴴ) i j
    exact (hmeas p).smul_const _
  have hXind : ProbabilityTheory.iIndepFun
      (fun p ω => ξ p ω • (R * laplCoeff p * Rᴴ)) μ := by
    refine hind.comp (fun p s => s • (R * laplCoeff p * Rᴴ)) fun p => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun s : ℝ => s • (R * laplCoeff p * Rᴴ) i j
    exact measurable_id.smul_const _
  have hε : (0 : ℝ) ≤ 1 - t := by linarith
  have hε1 : 1 - t < 1 := by linarith
  have h := matrix_chernoff_tail_lower (μ := μ) hXmeas hherm hmin hmax
    (by norm_num : (0 : ℝ) ≤ 2) hXind hε hε1
  have hmu : lambdaMin (isHermitian_sum_expectation (μ := μ) hherm) =
      prob * d := by
    rw [lambdaMin_congr (expectation_erY_eq (μ := μ) hprob hmeas hlaw hRR hRone)
      (isHermitian_sum_expectation (μ := μ) hherm)
      (isHermitian_real_smul Matrix.isHermitian_one _)]
    rw [lambdaMin_smul_nonneg Matrix.isHermitian_one
      (mul_nonneg hprob.1 (Nat.cast_nonneg d))
      (isHermitian_real_smul Matrix.isHermitian_one _), lambdaMin_one, mul_one]
  rw [hmu, show (1 : ℝ) - (1 - t) = t from by ring,
    show -(1 - t) = t - 1 from by ring] at h
  exact h

/-- **Book §5.3.3 final display** (C5-18):
`P(λ₂↑(Δ) ≤ t·pn) ≤ (n−1)·[e^{t−1}/t^t]^{pn/2}` for `t ∈ [0, 1)` — "To arrive
at a probability inequality for the second-smallest eigenvalue `λ₂↑(Δ)` … we
apply the tail bound (5.1.5) to the matrix `Y`", combined with the
Courant–Fischer identification (C5-15).

**Author note.** This pointwise-support form is retained for compatibility; see
`er_second_smallest_tail_of_isBernoulli` for the source-faithful law-only
sibling. -/
theorem er_second_smallest_tail [Nonempty W] {prob : ℝ}
    (hprob : prob ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ p, Measurable (ξ p)) (hlaw : ∀ p, IsBernoulli prob (ξ p) μ)
    (hrange : ∀ p ω, ξ p ω = 0 ∨ ξ p ω = 1)
    (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hRR : R * Rᴴ = 1) (hRone : R *ᵥ (fun _ => (1 : ℂ)) = 0)
    (hcard : Fintype.card W + 1 = d)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    μ.real {ω | secondSmallestEigenvalue
        (posSemidef_erLaplacian hrange ω).1 ≤ t * (prob * d)} ≤
      (Fintype.card W : ℝ) *
        (Real.exp (t - 1) / t ^ (t : ℝ)) ^ (prob * d / 2) := by
  classical
  have hdpos : 0 < d := by omega
  have hherm : ∀ (p : WignerIndex d) ω,
      ((fun p ω => ξ p ω • (R * laplCoeff p * Rᴴ)) p ω).IsHermitian :=
    fun p ω => isHermitian_compressed p R _
  -- the unit null vector `v = e/√n`
  set v : Fin d → ℂ := fun _ => (((Real.sqrt d)⁻¹ : ℝ) : ℂ) with hvdef
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have hsqpos : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hdpos)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hv : l2norm v = 1 := by
    have h1 : l2norm v ^ 2 = 1 := by
      rw [l2norm_sq]
      have h2 : ∀ i : Fin d, ‖v i‖ ^ 2 = ((Real.sqrt d)⁻¹) ^ 2 := fun i => by
        rw [hvdef]
        show ‖(((Real.sqrt d)⁻¹ : ℝ) : ℂ)‖ ^ 2 = _
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, inv_pow, hsq,
        mul_inv_cancel₀ (ne_of_gt hd0)]
    have h3 : (l2norm v - 1) * (l2norm v + 1) = 0 := by nlinarith [h1]
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · linarith [l2norm_nonneg v]
  have hvsmul : v = (((Real.sqrt d)⁻¹ : ℝ) : ℂ) • (fun _ : Fin d => (1 : ℂ)) := by
    rw [hvdef]
    funext i
    show (((Real.sqrt d)⁻¹ : ℝ) : ℂ) = (((Real.sqrt d)⁻¹ : ℝ) : ℂ) • (1 : ℂ)
    rw [smul_eq_mul, mul_one]
  have hAv : ∀ ω, erLaplacian ξ ω *ᵥ v = 0 := fun ω => by
    rw [hvsmul, Matrix.mulVec_smul, erLaplacian_mulVec_one, smul_zero]
  have hRv : R *ᵥ v = 0 := by
    rw [hvsmul, Matrix.mulVec_smul, hRone, smul_zero]
  have hcard' : Fintype.card W + 1 = Fintype.card (Fin d) := by
    rw [Fintype.card_fin]; exact hcard
  -- pointwise identification `λ_min(Y(ω)) = λ₂↑(Δ(ω))`
  have hid : ∀ ω,
      lambdaMin (isHermitian_matsum Finset.univ (fun p => hherm p ω)) =
        secondSmallestEigenvalue (posSemidef_erLaplacian hrange ω).1 := by
    intro ω
    have hRAR : (R * erLaplacian ξ ω * Rᴴ).IsHermitian :=
      ((posSemidef_erLaplacian hrange ω).mul_mul_conjTranspose_same R).1
    rw [lambdaMin_congr (compressed_sum_eq ξ R ω)
      (isHermitian_matsum Finset.univ (fun p => hherm p ω)) hRAR]
    exact lambdaMin_compression_eq_secondSmallest
      (posSemidef_erLaplacian hrange ω) hv (hAv ω) hRR hRv hcard' hRAR
  have hset : {ω | secondSmallestEigenvalue
        (posSemidef_erLaplacian hrange ω).1 ≤ t * (prob * d)} =
      {ω | lambdaMin (isHermitian_matsum Finset.univ (fun p => hherm p ω)) ≤
        t * (prob * d)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hid ω]
  rw [hset]
  exact er_compression_tail (μ := μ) hprob hmeas hlaw hrange hind hRR hRone
    hherm ht ht1


end CompressionTail

end MatrixConcentration


namespace MatrixConcentration

open Matrix Finset MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype n] [DecidableEq n] [Nonempty n]
variable {X : ι → Ω → Matrix n n ℂ}

/-- **Book §5.1.2.** Source-faithful integrable form of
`expectation_max_le_expectation_lambdaMax`: positive semidefiniteness is required
only almost surely, and integrability of the right-hand side replaces the auxiliary
uniform eigenvalue bound. -/
theorem expectation_max_le_expectation_lambdaMax_of_integrable
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmin : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (hherm k ω))
    (hint : Integrable (fun ω => lambdaMax
      (isHermitian_matsum Finset.univ (fun k => hherm k ω))) μ) :
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty
        (fun k => lambdaMax (hherm k ω)) ∂μ ≤
      ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ := by
  have hall : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ lambdaMin (hherm k ω) :=
    MeasureTheory.ae_all_iff.mpr hmin
  have hsupmeas : Measurable (fun ω => Finset.univ.sup' Finset.univ_nonempty
      (fun k => lambdaMax (hherm k ω))) := by
    have hm := Finset.measurable_sup' (s := (Finset.univ : Finset ι))
      Finset.univ_nonempty (f := fun k (ω : Ω) => lambdaMax (hherm k ω))
      (fun k _ => measurable_lambdaMax_of_forall (hmeas k) (hherm k))
    have heq : (Finset.univ.sup' Finset.univ_nonempty
        (fun k (ω : Ω) => lambdaMax (hherm k ω))) =
        fun ω => Finset.univ.sup' Finset.univ_nonempty
          (fun k => lambdaMax (hherm k ω)) := by
      funext ω
      exact Finset.sup'_apply _ _ _
    rwa [heq] at hm
  have hpoint : ∀ᵐ ω ∂μ, Finset.univ.sup' Finset.univ_nonempty
      (fun k => lambdaMax (hherm k ω)) ≤
      lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) := by
    filter_upwards [hall] with ω hω
    refine Finset.sup'_le _ _ fun k _ => ?_
    have hsplit : (∑ j, X j ω) = X k ω + ∑ j ∈ Finset.univ.erase k, X j ω :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
    have hrest : (∑ j ∈ Finset.univ.erase k, X j ω).PosSemidef :=
      posSemidef_matsum _ fun j => posSemidef_of_lambdaMin_nonneg
        (hherm j ω) (hω j)
    have hAH : (X k ω + ∑ j ∈ Finset.univ.erase k, X j ω).IsHermitian := by
      rw [← hsplit]
      exact isHermitian_matsum Finset.univ fun j => hherm j ω
    have h := lambdaMax_add_posSemidef_ge (hherm k ω) hrest hAH
    rwa [← lambdaMax_congr hsplit
      (isHermitian_matsum Finset.univ fun j => hherm j ω) hAH] at h
  have hsupint : Integrable (fun ω => Finset.univ.sup' Finset.univ_nonempty
      (fun k => lambdaMax (hherm k ω))) μ := by
    refine hint.mono_nonneg hsupmeas.aestronglyMeasurable ?_ hpoint
    filter_upwards [hall] with ω hω
    obtain ⟨k⟩ := (inferInstance : Nonempty ι)
    exact (hω k).trans ((lambdaMin_le_lambdaMax (hherm k ω)).trans
      (Finset.le_sup' (fun j => lambdaMax (hherm j ω)) (Finset.mem_univ k)))
  exact integral_mono_ae hsupint hint hpoint

end MatrixConcentration


/-!
# Almost-sure representatives for Bernoulli selectors

These source-facing siblings remove pointwise `0/1` assumptions by changing each
selector on its null exceptional set.  The measurable representative preserves its
law and joint independence, and all displayed expectations and events are transferred
back by almost-everywhere equality.
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

noncomputable def bernoulliRepresentative (x : ℝ) : ℝ :=
  if x = 0 ∨ x = 1 then x else 0

lemma measurable_bernoulliRepresentative : Measurable bernoulliRepresentative := by
  have hs : MeasurableSet {x : ℝ | x = 0 ∨ x = 1} := by
    convert (measurableSet_singleton (1 : ℝ)).union (measurableSet_singleton (0 : ℝ)) using 1
    ext x
    simp
  exact Measurable.ite hs measurable_id measurable_const

lemma bernoulliRepresentative_range (x : ℝ) :
    bernoulliRepresentative x = 0 ∨ bernoulliRepresentative x = 1 := by
  by_cases hx : x = 0 ∨ x = 1
  · simpa [bernoulliRepresentative, hx] using hx
  · simp [bernoulliRepresentative, hx]

lemma bernoulliRepresentative_ae_eq [IsProbabilityMeasure μ] {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) {f : Ω → ℝ}
    (hf : Measurable f) (hlaw : IsBernoulli p f μ) :
    (fun ω => bernoulliRepresentative (f ω)) =ᵐ[μ] f := by
  filter_upwards [ae_range_isBernoulli hp hf hlaw] with ω hω
  simp [bernoulliRepresentative, hω]

lemma isBernoulli_bernoulliRepresentative [IsProbabilityMeasure μ] {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) {f : Ω → ℝ}
    (hf : Measurable f) (hlaw : IsBernoulli p f μ) :
    IsBernoulli p (fun ω => bernoulliRepresentative (f ω)) μ := by
  unfold IsBernoulli
  rw [Measure.map_congr (bernoulliRepresentative_ae_eq hp hf hlaw), hlaw]

lemma iIndepFun_bernoulliRepresentative {ι : Type*} [IsProbabilityMeasure μ]
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {f : ι → Ω → ℝ}
    (hf : ∀ k, Measurable (f k)) (hlaw : ∀ k, IsBernoulli p (f k) μ)
    (hind : iIndepFun f μ) :
    iIndepFun (fun k ω => bernoulliRepresentative (f k ω)) μ := by
  exact hind.congr fun k => (bernoulliRepresentative_ae_eq hp (hf k) (hlaw k)).symm

lemma bernoulliRepresentative_all_ae {ι : Type*} [Countable ι]
    [IsProbabilityMeasure μ] {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {f : ι → Ω → ℝ} (hf : ∀ k, Measurable (f k))
    (hlaw : ∀ k, IsBernoulli p (f k) μ) :
    ∀ᵐ ω ∂μ, ∀ k, bernoulliRepresentative (f k ω) = f k ω :=
  MeasureTheory.ae_all_iff.mpr fun k => bernoulliRepresentative_ae_eq hp (hf k) (hlaw k)

lemma columnSubmatrix_congr_values {m n Ω' : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix m n ℂ) {δ δ' : n → Ω' → ℝ} {ω : Ω'}
    (h : ∀ k, δ k ω = δ' k ω) :
    columnSubmatrix B δ ω = columnSubmatrix B δ' ω := by
  unfold columnSubmatrix
  exact Finset.sum_congr rfl fun k _ => by rw [h k]

lemma rowSubmatrix_congr_values {d n Ω' : Type*} [Fintype d] [DecidableEq d]
    (B : Matrix d n ℂ) {δ δ' : d → Ω' → ℝ} {ω : Ω'}
    (h : ∀ j, δ j ω = δ' j ω) :
    rowSubmatrix B δ ω = rowSubmatrix B δ' ω := by
  unfold rowSubmatrix projDiag
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [h i]
  · simp [hij]

section BernoulliColumnWrappers

variable {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n] [Nonempty n] [IsProbabilityMeasure μ]

/-- **Book (5.2.1), upper half.** Source-faithful sibling of
`column_submatrix_upper`, using only the Bernoulli law. -/
theorem column_submatrix_upper_of_isBernoulli (B : Matrix m n ℂ) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) {δ : n → Ω → ℝ}
    (hmeas : ∀ k, Measurable (δ k)) (hlaw : ∀ k, IsBernoulli q (δ k) μ)
    (hind : iIndepFun δ μ) :
    ∫ ω, lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (columnSubmatrix B δ ω)) ∂μ ≤
      1.72 * (q * lambdaMax (Matrix.isHermitian_mul_conjTranspose_self B)) +
        Real.log (Fintype.card m) *
          Finset.univ.sup' Finset.univ_nonempty (colNormSq B) := by
  let δ' : n → Ω → ℝ := fun k ω => bernoulliRepresentative (δ k ω)
  have hm' : ∀ k, Measurable (δ' k) := fun k =>
    measurable_bernoulliRepresentative.comp (hmeas k)
  have hl' : ∀ k, IsBernoulli q (δ' k) μ := fun k =>
    isBernoulli_bernoulliRepresentative hq (hmeas k) (hlaw k)
  have hi' : iIndepFun δ' μ := iIndepFun_bernoulliRepresentative hq hmeas hlaw hind
  have hr' : ∀ k ω, δ' k ω = 0 ∨ δ' k ω = 1 := fun k ω =>
    bernoulliRepresentative_range (δ k ω)
  have hmain := column_submatrix_upper (μ := μ) B hq hm' hl' hr' hi'
  have hall := bernoulliRepresentative_all_ae hq hmeas hlaw
  have hint : (fun ω => lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
      (columnSubmatrix B δ' ω))) =ᵐ[μ]
      fun ω => lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (columnSubmatrix B δ ω)) := by
    filter_upwards [hall] with ω hω
    have hmat : columnSubmatrix B δ' ω = columnSubmatrix B δ ω :=
      columnSubmatrix_congr_values B hω
    exact lambdaMax_congr (by rw [hmat]) _ _
  rwa [integral_congr_ae hint] at hmain

/-- **Book (5.2.1), lower half.** Source-faithful sibling of
`column_submatrix_lower`, using only the Bernoulli law. -/
theorem column_submatrix_lower_of_isBernoulli (B : Matrix m n ℂ) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) {δ : n → Ω → ℝ}
    (hmeas : ∀ k, Measurable (δ k)) (hlaw : ∀ k, IsBernoulli q (δ k) μ)
    (hind : iIndepFun δ μ) :
    0.63 * (q * lambdaMin (Matrix.isHermitian_mul_conjTranspose_self B)) -
        Real.log (Fintype.card m) *
          Finset.univ.sup' Finset.univ_nonempty (colNormSq B) ≤
      ∫ ω, lambdaMin (Matrix.isHermitian_mul_conjTranspose_self
        (columnSubmatrix B δ ω)) ∂μ := by
  let δ' : n → Ω → ℝ := fun k ω => bernoulliRepresentative (δ k ω)
  have hm' : ∀ k, Measurable (δ' k) := fun k =>
    measurable_bernoulliRepresentative.comp (hmeas k)
  have hl' : ∀ k, IsBernoulli q (δ' k) μ := fun k =>
    isBernoulli_bernoulliRepresentative hq (hmeas k) (hlaw k)
  have hi' : iIndepFun δ' μ := iIndepFun_bernoulliRepresentative hq hmeas hlaw hind
  have hr' : ∀ k ω, δ' k ω = 0 ∨ δ' k ω = 1 := fun k ω =>
    bernoulliRepresentative_range (δ k ω)
  have hmain := column_submatrix_lower (μ := μ) B hq hm' hl' hr' hi'
  have hall := bernoulliRepresentative_all_ae hq hmeas hlaw
  have hint : (fun ω => lambdaMin (Matrix.isHermitian_mul_conjTranspose_self
      (columnSubmatrix B δ' ω))) =ᵐ[μ]
      fun ω => lambdaMin (Matrix.isHermitian_mul_conjTranspose_self
        (columnSubmatrix B δ ω)) := by
    filter_upwards [hall] with ω hω
    have hmat : columnSubmatrix B δ' ω = columnSubmatrix B δ ω :=
      columnSubmatrix_congr_values B hω
    exact lambdaMin_congr (by rw [hmat]) _ _
  rwa [integral_congr_ae hint] at hmain

end BernoulliColumnWrappers

section BernoulliRowWrappers

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : MeasureTheory.Measure Ω₁} {μ₂ : MeasureTheory.Measure Ω₂}
variable [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
variable {d n : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
variable [Fintype n] [DecidableEq n] [Nonempty n]

/-- **Book (5.2.3), conditional step.** Source-faithful sibling of
`conditional_column_bound_pointwise`; the column selectors need only have the
Bernoulli law. -/
theorem conditional_column_bound_pointwise_of_isBernoulli
    {B : Matrix d n ℂ} {δ : d → Ω₁ → ℝ} {ξ : n → Ω₂ → ℝ} {rq : ℝ}
    (hrq : rq ∈ Set.Icc (0 : ℝ) 1)
    (hξmeas : ∀ k, Measurable (ξ k)) (hξlaw : ∀ k, IsBernoulli rq (ξ k) μ₂)
    (hξind : iIndepFun ξ μ₂) (ω₁ : Ω₁) :
    ∫ ω₂, lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (rowColumnSubmatrix B δ ξ ω₁ ω₂)) ∂μ₂ ≤
      1.72 * (rq * lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
          (rowSubmatrix B δ ω₁))) +
        Real.log (Fintype.card d) * Finset.univ.sup' Finset.univ_nonempty
          (colNormSq (rowSubmatrix B δ ω₁)) := by
  let ξ' : n → Ω₂ → ℝ := fun k ω => bernoulliRepresentative (ξ k ω)
  have hm' : ∀ k, Measurable (ξ' k) := fun k =>
    measurable_bernoulliRepresentative.comp (hξmeas k)
  have hl' : ∀ k, IsBernoulli rq (ξ' k) μ₂ := fun k =>
    isBernoulli_bernoulliRepresentative hrq (hξmeas k) (hξlaw k)
  have hi' : iIndepFun ξ' μ₂ :=
    iIndepFun_bernoulliRepresentative hrq hξmeas hξlaw hξind
  have hr' : ∀ k ω, ξ' k ω = 0 ∨ ξ' k ω = 1 := fun k ω =>
    bernoulliRepresentative_range (ξ k ω)
  have hmain := conditional_column_bound_pointwise (μ₂ := μ₂) (B := B) (δ := δ)
    hrq hm' hl' hr' hi' ω₁
  have hall := bernoulliRepresentative_all_ae hrq hξmeas hξlaw
  have hint : (fun ω₂ => lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
      (rowColumnSubmatrix B δ ξ' ω₁ ω₂))) =ᵐ[μ₂]
      fun ω₂ => lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (rowColumnSubmatrix B δ ξ ω₁ ω₂)) := by
    filter_upwards [hall] with ω₂ hω
    have hmat : rowColumnSubmatrix B δ ξ' ω₁ ω₂ =
        rowColumnSubmatrix B δ ξ ω₁ ω₂ :=
      columnSubmatrix_congr_values (rowSubmatrix B δ ω₁) hω
    exact lambdaMax_congr (by rw [hmat]) _ _
  rwa [integral_congr_ae hint] at hmain

/-- **Book (5.2.4).** Source-faithful sibling of `row_sampling_gram_bound`. -/
theorem row_sampling_gram_bound_of_isBernoulli
    {B : Matrix d n ℂ} {δ : d → Ω₁ → ℝ} {pq : ℝ}
    (hpq : pq ∈ Set.Icc (0 : ℝ) 1)
    (hδmeas : ∀ j, Measurable (δ j)) (hδlaw : ∀ j, IsBernoulli pq (δ j) μ₁)
    (hδind : iIndepFun δ μ₁) :
    ∫ ω₁, lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (rowSubmatrix B δ ω₁)) ∂μ₁ ≤
      1.72 * (pq * ‖B‖ ^ 2) +
        Real.log (Fintype.card n) * Finset.univ.sup' Finset.univ_nonempty
          (fun j => ∑ k, ‖B j k‖ ^ 2) := by
  let δ' : d → Ω₁ → ℝ := fun j ω => bernoulliRepresentative (δ j ω)
  have hm' : ∀ j, Measurable (δ' j) := fun j =>
    measurable_bernoulliRepresentative.comp (hδmeas j)
  have hl' : ∀ j, IsBernoulli pq (δ' j) μ₁ := fun j =>
    isBernoulli_bernoulliRepresentative hpq (hδmeas j) (hδlaw j)
  have hi' : iIndepFun δ' μ₁ :=
    iIndepFun_bernoulliRepresentative hpq hδmeas hδlaw hδind
  have hr' : ∀ j ω, δ' j ω = 0 ∨ δ' j ω = 1 := fun j ω =>
    bernoulliRepresentative_range (δ j ω)
  have hmain := row_sampling_gram_bound (μ₁ := μ₁) (B := B)
    hpq hm' hl' hr' hi'
  have hall := bernoulliRepresentative_all_ae hpq hδmeas hδlaw
  have hint : (fun ω₁ => lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
      (rowSubmatrix B δ' ω₁))) =ᵐ[μ₁]
      fun ω₁ => lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (rowSubmatrix B δ ω₁)) := by
    filter_upwards [hall] with ω₁ hω
    have hmat := rowSubmatrix_congr_values B (δ := δ') (δ' := δ) (ω := ω₁) hω
    exact lambdaMax_congr (by rw [hmat]) _ _
  rwa [integral_congr_ae hint] at hmain

/-- **Book (5.2.5).** Source-faithful sibling of `max_column_norm_bound`. -/
theorem max_column_norm_bound_of_isBernoulli
    {B : Matrix d n ℂ} {δ : d → Ω₁ → ℝ} {pq : ℝ}
    (hpq : pq ∈ Set.Icc (0 : ℝ) 1)
    (hδmeas : ∀ j, Measurable (δ j)) (hδlaw : ∀ j, IsBernoulli pq (δ j) μ₁)
    (hδind : iIndepFun δ μ₁) :
    ∫ ω₁, Finset.univ.sup' Finset.univ_nonempty
        (colNormSq (rowSubmatrix B δ ω₁)) ∂μ₁ ≤
      1.72 * (pq * Finset.univ.sup' Finset.univ_nonempty (colNormSq B)) +
        Real.log (Fintype.card n) * Finset.univ.sup' Finset.univ_nonempty
          (fun j => Finset.univ.sup' Finset.univ_nonempty
            (fun k => ‖B j k‖ ^ 2)) := by
  let δ' : d → Ω₁ → ℝ := fun j ω => bernoulliRepresentative (δ j ω)
  have hm' : ∀ j, Measurable (δ' j) := fun j =>
    measurable_bernoulliRepresentative.comp (hδmeas j)
  have hl' : ∀ j, IsBernoulli pq (δ' j) μ₁ := fun j =>
    isBernoulli_bernoulliRepresentative hpq (hδmeas j) (hδlaw j)
  have hi' : iIndepFun δ' μ₁ :=
    iIndepFun_bernoulliRepresentative hpq hδmeas hδlaw hδind
  have hr' : ∀ j ω, δ' j ω = 0 ∨ δ' j ω = 1 := fun j ω =>
    bernoulliRepresentative_range (δ j ω)
  have hmain := max_column_norm_bound (μ₁ := μ₁) (B := B)
    hpq hm' hl' hr' hi'
  have hall := bernoulliRepresentative_all_ae hpq hδmeas hδlaw
  have hint : (fun ω₁ => Finset.univ.sup' Finset.univ_nonempty
      (colNormSq (rowSubmatrix B δ' ω₁))) =ᵐ[μ₁]
      fun ω₁ => Finset.univ.sup' Finset.univ_nonempty
        (colNormSq (rowSubmatrix B δ ω₁)) := by
    filter_upwards [hall] with ω₁ hω
    rw [rowSubmatrix_congr_values B (δ := δ') (δ' := δ) (ω := ω₁) hω]
  rwa [integral_congr_ae hint] at hmain

/-- **Book (5.2.3).** Source-faithful counterpart of
`conditional_column_bound`: both selector families are used through their
Bernoulli laws, with no pointwise support premise. -/
theorem conditional_column_bound_of_isBernoulli
    {B : Matrix d n ℂ} {δ : d → Ω₁ → ℝ} {ξ : n → Ω₂ → ℝ} {pq rq : ℝ}
    (hpq : pq ∈ Set.Icc (0 : ℝ) 1) (hrq : rq ∈ Set.Icc (0 : ℝ) 1)
    (hδmeas : ∀ j, Measurable (δ j)) (hδlaw : ∀ j, IsBernoulli pq (δ j) μ₁)
    (hξmeas : ∀ k, Measurable (ξ k)) (hξlaw : ∀ k, IsBernoulli rq (ξ k) μ₂)
    (hξind : iIndepFun ξ μ₂) :
    ∫ ω₁, (∫ ω₂, ‖rowColumnSubmatrix B δ ξ ω₁ ω₂‖ ^ 2 ∂μ₂) ∂μ₁ ≤
      1.72 * (rq * ∫ ω₁, lambdaMax
          (Matrix.isHermitian_mul_conjTranspose_self
            (rowSubmatrix B δ ω₁)) ∂μ₁) +
        Real.log (Fintype.card d) *
          ∫ ω₁, Finset.univ.sup' Finset.univ_nonempty
            (colNormSq (rowSubmatrix B δ ω₁)) ∂μ₁ := by
  let δ' : d → Ω₁ → ℝ := fun j ω => bernoulliRepresentative (δ j ω)
  let ξ' : n → Ω₂ → ℝ := fun k ω => bernoulliRepresentative (ξ k ω)
  have hδm' : ∀ j, Measurable (δ' j) := fun j =>
    measurable_bernoulliRepresentative.comp (hδmeas j)
  have hξm' : ∀ k, Measurable (ξ' k) := fun k =>
    measurable_bernoulliRepresentative.comp (hξmeas k)
  have hξl' : ∀ k, IsBernoulli rq (ξ' k) μ₂ := fun k =>
    isBernoulli_bernoulliRepresentative hrq (hξmeas k) (hξlaw k)
  have hξi' : iIndepFun ξ' μ₂ :=
    iIndepFun_bernoulliRepresentative hrq hξmeas hξlaw hξind
  have hδr' : ∀ j ω, δ' j ω = 0 ∨ δ' j ω = 1 := fun j ω =>
    bernoulliRepresentative_range (δ j ω)
  have hξr' : ∀ k ω, ξ' k ω = 0 ∨ ξ' k ω = 1 := fun k ω =>
    bernoulliRepresentative_range (ξ k ω)
  have hmain := conditional_column_bound (μ₁ := μ₁) (μ₂ := μ₂) (B := B)
    hrq hδm' hδr' hξm' hξl' hξr' hξi'
  have hallδ := bernoulliRepresentative_all_ae hpq hδmeas hδlaw
  have hallξ := bernoulliRepresentative_all_ae hrq hξmeas hξlaw
  have hlhs : (fun ω₁ => ∫ ω₂, ‖rowColumnSubmatrix B δ' ξ' ω₁ ω₂‖ ^ 2 ∂μ₂) =ᵐ[μ₁]
      fun ω₁ => ∫ ω₂, ‖rowColumnSubmatrix B δ ξ ω₁ ω₂‖ ^ 2 ∂μ₂ := by
    filter_upwards [hallδ] with ω₁ hδω
    apply integral_congr_ae
    filter_upwards [hallξ] with ω₂ hξω
    have hrow : rowSubmatrix B δ' ω₁ = rowSubmatrix B δ ω₁ :=
      rowSubmatrix_congr_values B (δ := δ') (δ' := δ) (ω := ω₁) hδω
    have hmat : rowColumnSubmatrix B δ' ξ' ω₁ ω₂ =
        rowColumnSubmatrix B δ ξ ω₁ ω₂ := by
      unfold rowColumnSubmatrix
      rw [hrow]
      exact columnSubmatrix_congr_values _ hξω
    rw [hmat]
  have hgram : (fun ω₁ => lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
      (rowSubmatrix B δ' ω₁))) =ᵐ[μ₁]
      fun ω₁ => lambdaMax (Matrix.isHermitian_mul_conjTranspose_self
        (rowSubmatrix B δ ω₁)) := by
    filter_upwards [hallδ] with ω₁ hδω
    have hrow := rowSubmatrix_congr_values B
      (δ := δ') (δ' := δ) (ω := ω₁) hδω
    exact lambdaMax_congr (by rw [hrow]) _ _
  have hsup : (fun ω₁ => Finset.univ.sup' Finset.univ_nonempty
      (colNormSq (rowSubmatrix B δ' ω₁))) =ᵐ[μ₁]
      fun ω₁ => Finset.univ.sup' Finset.univ_nonempty
        (colNormSq (rowSubmatrix B δ ω₁)) := by
    filter_upwards [hallδ] with ω₁ hδω
    rw [rowSubmatrix_congr_values B (δ := δ') (δ' := δ) (ω := ω₁) hδω]
  rw [integral_congr_ae hlhs, integral_congr_ae hgram,
    integral_congr_ae hsup] at hmain
  exact hmain

/-- **Book (5.2.2).** Source-faithful counterpart of
`row_column_submatrix_norm`, with Bernoulli support derived almost surely from
each law. -/
theorem row_column_submatrix_norm_of_isBernoulli
    {B : Matrix d n ℂ} {δ : d → Ω₁ → ℝ} {ξ : n → Ω₂ → ℝ} {pq rq : ℝ}
    (hpq : pq ∈ Set.Icc (0 : ℝ) 1) (hrq : rq ∈ Set.Icc (0 : ℝ) 1)
    (hδmeas : ∀ j, Measurable (δ j)) (hδlaw : ∀ j, IsBernoulli pq (δ j) μ₁)
    (hδind : iIndepFun δ μ₁)
    (hξmeas : ∀ k, Measurable (ξ k)) (hξlaw : ∀ k, IsBernoulli rq (ξ k) μ₂)
    (hξind : iIndepFun ξ μ₂) :
    ∫ ω₁, (∫ ω₂, ‖rowColumnSubmatrix B δ ξ ω₁ ω₂‖ ^ 2 ∂μ₂) ∂μ₁ ≤
      3 * (pq * rq * ‖B‖ ^ 2) +
        2 * (pq * Real.log (Fintype.card d)) *
          Finset.univ.sup' Finset.univ_nonempty (colNormSq B) +
        2 * (rq * Real.log (Fintype.card n)) *
          Finset.univ.sup' Finset.univ_nonempty
            (fun j => ∑ k, ‖B j k‖ ^ 2) +
        Real.log (Fintype.card d) * Real.log (Fintype.card n) *
          Finset.univ.sup' Finset.univ_nonempty
            (fun j => Finset.univ.sup' Finset.univ_nonempty
              (fun k => ‖B j k‖ ^ 2)) := by
  let δ' : d → Ω₁ → ℝ := fun j ω => bernoulliRepresentative (δ j ω)
  let ξ' : n → Ω₂ → ℝ := fun k ω => bernoulliRepresentative (ξ k ω)
  have hδm' : ∀ j, Measurable (δ' j) := fun j =>
    measurable_bernoulliRepresentative.comp (hδmeas j)
  have hδl' : ∀ j, IsBernoulli pq (δ' j) μ₁ := fun j =>
    isBernoulli_bernoulliRepresentative hpq (hδmeas j) (hδlaw j)
  have hδi' : iIndepFun δ' μ₁ :=
    iIndepFun_bernoulliRepresentative hpq hδmeas hδlaw hδind
  have hξm' : ∀ k, Measurable (ξ' k) := fun k =>
    measurable_bernoulliRepresentative.comp (hξmeas k)
  have hξl' : ∀ k, IsBernoulli rq (ξ' k) μ₂ := fun k =>
    isBernoulli_bernoulliRepresentative hrq (hξmeas k) (hξlaw k)
  have hξi' : iIndepFun ξ' μ₂ :=
    iIndepFun_bernoulliRepresentative hrq hξmeas hξlaw hξind
  have hδr' : ∀ j ω, δ' j ω = 0 ∨ δ' j ω = 1 := fun j ω =>
    bernoulliRepresentative_range (δ j ω)
  have hξr' : ∀ k ω, ξ' k ω = 0 ∨ ξ' k ω = 1 := fun k ω =>
    bernoulliRepresentative_range (ξ k ω)
  have hmain := row_column_submatrix_norm (μ₁ := μ₁) (μ₂ := μ₂) (B := B)
    hpq hrq hδm' hδl' hδr' hδi' hξm' hξl' hξr' hξi'
  have hallδ := bernoulliRepresentative_all_ae hpq hδmeas hδlaw
  have hallξ := bernoulliRepresentative_all_ae hrq hξmeas hξlaw
  have hlhs : (fun ω₁ => ∫ ω₂, ‖rowColumnSubmatrix B δ' ξ' ω₁ ω₂‖ ^ 2 ∂μ₂) =ᵐ[μ₁]
      fun ω₁ => ∫ ω₂, ‖rowColumnSubmatrix B δ ξ ω₁ ω₂‖ ^ 2 ∂μ₂ := by
    filter_upwards [hallδ] with ω₁ hδω
    apply integral_congr_ae
    filter_upwards [hallξ] with ω₂ hξω
    have hrow : rowSubmatrix B δ' ω₁ = rowSubmatrix B δ ω₁ :=
      rowSubmatrix_congr_values B (δ := δ') (δ' := δ) (ω := ω₁) hδω
    have hmat : rowColumnSubmatrix B δ' ξ' ω₁ ω₂ =
        rowColumnSubmatrix B δ ξ ω₁ ω₂ := by
      unfold rowColumnSubmatrix
      rw [hrow]
      exact columnSubmatrix_congr_values _ hξω
    rw [hmat]
  rwa [integral_congr_ae hlhs] at hmain

end BernoulliRowWrappers

section BernoulliErdosRenyiWrappers

variable {d : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
variable {ξ : WignerIndex d → Ω → ℝ} {R : Matrix W (Fin d) ℂ}
variable [IsProbabilityMeasure μ]

lemma isHermitian_erLaplacian (ξ : WignerIndex d → Ω → ℝ) (ω : Ω) :
    (erLaplacian ξ ω).IsHermitian := by
  unfold erLaplacian
  exact isHermitian_matsum Finset.univ fun p =>
    isHermitian_real_smul (posSemidef_laplCoeff p).1 _

lemma secondSmallestEigenvalue_congr {V : Type*} [Fintype V] [DecidableEq V]
    {A B : Matrix V V ℂ} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    secondSmallestEigenvalue hA = secondSmallestEigenvalue hB := by
  subst B
  rfl

/-- **Book §5.3.3, compression display.** Source-faithful counterpart of
`er_compression_tail`: the Bernoulli range is derived almost surely from the
law, and the event is stated for the original representatives. -/
theorem er_compression_tail_of_isBernoulli [Nonempty W] {prob : ℝ}
    (hprob : prob ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ p, Measurable (ξ p)) (hlaw : ∀ p, IsBernoulli prob (ξ p) μ)
    (hind : iIndepFun ξ μ)
    (hRR : R * Rᴴ = 1) (hRone : R *ᵥ (fun _ => (1 : ℂ)) = 0)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    μ.real {ω | lambdaMin (isHermitian_matsum Finset.univ
        (fun p => isHermitian_compressed p R (ξ p ω))) ≤ t * (prob * d)} ≤
      (Fintype.card W : ℝ) *
        (Real.exp (t - 1) / t ^ (t : ℝ)) ^ (prob * d / 2) := by
  let ξ' : WignerIndex d → Ω → ℝ := fun p ω => bernoulliRepresentative (ξ p ω)
  have hm' : ∀ p, Measurable (ξ' p) := fun p =>
    measurable_bernoulliRepresentative.comp (hmeas p)
  have hl' : ∀ p, IsBernoulli prob (ξ' p) μ := fun p =>
    isBernoulli_bernoulliRepresentative hprob (hmeas p) (hlaw p)
  have hi' : iIndepFun ξ' μ :=
    iIndepFun_bernoulliRepresentative hprob hmeas hlaw hind
  have hr' : ∀ p ω, ξ' p ω = 0 ∨ ξ' p ω = 1 := fun p ω =>
    bernoulliRepresentative_range (ξ p ω)
  have hherm' : ∀ (p : WignerIndex d) ω,
      (ξ' p ω • (R * laplCoeff p * Rᴴ)).IsHermitian := fun p ω =>
    isHermitian_compressed p R _
  have hmain := er_compression_tail (μ := μ) hprob hm' hl' hr' hi'
    hRR hRone hherm' ht ht1
  have hall := bernoulliRepresentative_all_ae hprob hmeas hlaw
  have hsum : (fun ω => ∑ p, ξ' p ω • (R * laplCoeff p * Rᴴ)) =ᵐ[μ]
      fun ω => ∑ p, ξ p ω • (R * laplCoeff p * Rᴴ) := by
    filter_upwards [hall] with ω hω
    exact Finset.sum_congr rfl fun p _ => by
      change bernoulliRepresentative (ξ p ω) • (R * laplCoeff p * Rᴴ) = _
      rw [hω p]
  have hevent : {ω | lambdaMin (isHermitian_matsum Finset.univ
      (fun p => hherm' p ω)) ≤ t * (prob * d)} =ᵐ[μ]
      {ω | lambdaMin (isHermitian_matsum Finset.univ
        (fun p => isHermitian_compressed p R (ξ p ω))) ≤ t * (prob * d)} := by
    filter_upwards [hsum] with ω hω
    change (lambdaMin (isHermitian_matsum Finset.univ
      (fun p => hherm' p ω)) ≤ t * (prob * d)) =
      (lambdaMin (isHermitian_matsum Finset.univ
        (fun p => isHermitian_compressed p R (ξ p ω))) ≤ t * (prob * d))
    apply propext
    rw [lambdaMin_congr hω _ _]
  rwa [measureReal_congr hevent] at hmain

/-- **Book §5.3.3, second-smallest-eigenvalue display.** Source-faithful
counterpart of `er_second_smallest_tail`, with no pointwise support premise. -/
theorem er_second_smallest_tail_of_isBernoulli [Nonempty W] {prob : ℝ}
    (hprob : prob ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ p, Measurable (ξ p)) (hlaw : ∀ p, IsBernoulli prob (ξ p) μ)
    (hind : iIndepFun ξ μ)
    (hRR : R * Rᴴ = 1) (hRone : R *ᵥ (fun _ => (1 : ℂ)) = 0)
    (hcard : Fintype.card W + 1 = d)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    μ.real {ω | secondSmallestEigenvalue (isHermitian_erLaplacian ξ ω) ≤
        t * (prob * d)} ≤
      (Fintype.card W : ℝ) *
        (Real.exp (t - 1) / t ^ (t : ℝ)) ^ (prob * d / 2) := by
  let ξ' : WignerIndex d → Ω → ℝ := fun p ω => bernoulliRepresentative (ξ p ω)
  have hm' : ∀ p, Measurable (ξ' p) := fun p =>
    measurable_bernoulliRepresentative.comp (hmeas p)
  have hl' : ∀ p, IsBernoulli prob (ξ' p) μ := fun p =>
    isBernoulli_bernoulliRepresentative hprob (hmeas p) (hlaw p)
  have hi' : iIndepFun ξ' μ :=
    iIndepFun_bernoulliRepresentative hprob hmeas hlaw hind
  have hr' : ∀ p ω, ξ' p ω = 0 ∨ ξ' p ω = 1 := fun p ω =>
    bernoulliRepresentative_range (ξ p ω)
  have hmain := er_second_smallest_tail (μ := μ) hprob hm' hl' hr' hi'
    hRR hRone hcard ht ht1
  have hall := bernoulliRepresentative_all_ae hprob hmeas hlaw
  have hmat : (fun ω => erLaplacian ξ' ω) =ᵐ[μ] fun ω => erLaplacian ξ ω := by
    filter_upwards [hall] with ω hω
    unfold erLaplacian
    exact Finset.sum_congr rfl fun p _ => by
      change bernoulliRepresentative (ξ p ω) • laplCoeff p = _
      rw [hω p]
  have hevent : {ω | secondSmallestEigenvalue
      (posSemidef_erLaplacian hr' ω).1 ≤ t * (prob * d)} =ᵐ[μ]
      {ω | secondSmallestEigenvalue (isHermitian_erLaplacian ξ ω) ≤
        t * (prob * d)} := by
    filter_upwards [hmat] with ω hω
    change (secondSmallestEigenvalue (posSemidef_erLaplacian hr' ω).1 ≤
      t * (prob * d)) =
      (secondSmallestEigenvalue (isHermitian_erLaplacian ξ ω) ≤ t * (prob * d))
    apply propext
    rw [secondSmallestEigenvalue_congr hω _ _]
  rwa [measureReal_congr hevent] at hmain

end BernoulliErdosRenyiWrappers

end MatrixConcentration
