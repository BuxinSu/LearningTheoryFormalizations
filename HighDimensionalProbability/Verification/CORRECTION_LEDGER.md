# Correction ledger

This ledger records validated corrections against the original second-edition
PDF. `archive/REVIEW_NOTES.pre-final-correction.md` is the verbatim frozen Pass 05
input audit; the live `REVIEW_NOTES.md` is the authoritative active-coverage
overlay on the open Round 11 layout/change phase of the Pass 07 audit.

## Pass 07 final-correction dispositions

The Pass 05 catalogue contained 14 findings.  Independent PDF and Lean
validation classified **9 CONFIRMED**, **4 REVISED**, and **1 REJECTED**.
“Confirmed, already actioned” means Pass 05 itself had already corrected the
publication mapping; Pass 07 revalidated it and made no redundant code edit.

| ID | Input severity | Verdict | PDF-grounded evidence and Pass 07 action | Outcome |
|---|---|---|---|---|
| F-01 | critical | CONFIRMED | **Book Exercise 3.19** defines GOE by independent upper-triangular entries, identifies it with `(G+Gᵀ)/√2`, and proves orthogonal-conjugation invariance. Replaced the abstract image-by-definition interface with `independentGOEMatrixMeasure`, explicit diagonal `N(0,2)` and off-diagonal `N(0,1)` laws, upper-coordinate independence, concrete symmetrization, and conjugation. | FIXED in correction round 1; reverified in round 5. |
| F-02 | critical | CONFIRMED | **Book Exercise 3.20** begins with one Ginibre matrix and orthogonal unit vectors. `exercise_3_20` now proves independence and both standard-Gaussian image laws for the concrete maps `A ↦ Au` and `A ↦ Av` under `stdGaussianMatrixMeasure`. | FIXED in correction round 1; reverified in round 5. |
| F-03 | critical | CONFIRMED; SCOPE REMOVED | **Book equation (5.8)** quantifies over a compact connected Riemannian manifold with normalized volume and an actual Ricci lower bound. The former Appendix theorem instead required an explicit `RiemannianDiffusionLaw`. Because that was not source-faithful coverage, the source-facing module, its three theorems, the registry row, and the active census row were removed on 2026-07-20. | RESOLVED BY REMOVAL; equation (5.8) is explicitly outside active coverage. |
| F-04 | critical | CONFIRMED | **Book Remark 7.2.1** uses a supremum of finite-subfamily expectations that may be infinite. Added `extendedExpectation : EReal`, its integrable bridge, and rebuilt `extendedExpectedSupremum` from extended finite stages. | FIXED in correction round 1; reverified in round 5. |
| F-05 | critical | CONFIRMED | **Book equation (8.37)** permits infinite squared risk. Changed `populationRisk` to `ℝ≥0∞`, added the proof-carrying real `finitePopulationRisk`, bridges, and safe minimizer/learning engines. | FIXED in correction round 1; reverified through the Chapter 8 exercise dependency cone. |
| F-06 | major | CONFIRMED | **Book Exercise 3.18** is specifically Ginibre invariance under left/right multiplication by orthogonal matrices. Added concrete actions, vectorized linear isometries, law-invariance theorems, and the exact exercise wrapper. | FIXED in correction round 1; reverified in round 5. |
| F-07 | major | REVISED | The raw `SubGaussian`/`SubExponential` predicates are useful generalized analytic helpers; deleting them would create unnecessary churn. The source-facing omission was the lack of bundled random-variable predicates. Added `IsSubGaussianRandomVariable` and `IsSubExponentialRandomVariable`, probability/measurability iff bridges, and bundled attained-norm MGF theorems. | FIXED ADDITIVELY; raw callers preserved and source mappings moved to the bundled APIs. |
| F-08 | major | REVISED | The raw totalized `IsIsotropic` equation remains a useful helper. The source-facing gap was the absent probability/measurability/`MemLp 2` package. Added `IsIsotropicRandomVector`, its iff bridge, coordinate-product integrability, and the directional equation (3.9) endpoint. | FIXED ADDITIVELY; raw dependency cone preserved. |
| F-09 | major | REVISED | The real `sSup` helper may remain generalized, but the book-facing vector predicate must derive its finite supremum domain. Added `IsSubGaussianRandomVector`, scalar-marginal packaging, a finite-dimensional proof of `psi2NormSet_bddAbove`, and the bundled marginal comparison. | FIXED ADDITIVELY; no source-facing boundedness premise remains. |
| F-10 | major | CONFIRMED | **Book Definition 3.3.4** requires a covariance matrix. Added `S.PosSemidef` to `HasGaussianVectorLaw`; rechecked its affine-representation theorem and both exercise consumers. | FIXED in correction round 1; dependency cone reverified. |
| F-11 | major | REVISED | The finite real helpers are legitimate on their documented domains; the missing general object was an extended MGF. Added `extendedMGF` and its integrable bridge, and made every raw real helper's off-domain convention explicit. | FIXED ADDITIVELY; finite-domain consumers unchanged. |
| F-12 | major, record | CONFIRMED, ALREADY ACTIONED | **Book equation (7.14)** is arbitrary-index. Pass 05 had already remapped it to `extendedExpectedSupremum` and retained `expectedFiniteSupremum` only as the finite engine. Pass 07 revalidated that endpoint after F-04. | VALIDATED; no separate code change. |
| F-13 | major, record | CONFIRMED, ALREADY ACTIONED | **Book Theorem 7.6.1** treats every nonempty bounded set. Pass 05 had already remapped it to `haarProjection_expectedDiameter_set`, with the finite theorem named only as its engine. | VALIDATED; no separate code change. |
| F-14 | minor | REJECTED / STRONGER | The source ratio is used for positive conditioning probability. `cond_real` agrees there and adds a documented zero-denominator extension; it asserts no false positive-domain theorem. | NO CHANGE. |

## Historical Pass 06 soundness-finding dispositions

All 25 non-INFO findings from the nine mechanical reports were independently
validated. Their validation totals are **10 CONFIRMED / 14 REVISED /
1 REJECTED**. The exhaustive machine-readable record, including original
severity, evidence path, action, and current state for every stable ID, is
`Verification/inventory/pass07_soundness_resolutions.tsv`.  This is the
historical pre-restructuring Pass 06 population; the current V1--V10 findings
are adjudicated separately below.

| Current state | Stable IDs | Validation accounting | Resolution |
|---|---|---:|---|
| `FIXED` | V2-F2, V3-F2, V6-F2, V6-F6, V9-F3, V9-F4, V9-F6, V9-F8 | 7 confirmed + 1 revised | Wired the Berry--Esseen smoothing module; reconciled the live placeholder/registry records; repaired the reflexive Bernoulli helper; added historical endpoint-key overlays; corrected publication counts, names, and documentation scope. |
| `OUT_OF_SCOPE_BLOCKER` | V1-F1, V2-F1, V3-F1, V4-F1, V6-F1, V7-F1, V8-F1, V9-F1, V9-F2 | 9 revised | These were nine views of one Rosenthal--Pinelis build failure and its three dependent modules in the former frozen `Pre_MatrixConcentration/` layout.  The current tree has no such subtree or orphan module. |
| `RESOLVED_BY_REMOVAL` | V6-F7 | 1 revised | On 2026-07-20 the arbitrary-set Chevet class, five conditional consumers, and Appendix wrapper/module were deleted. The direct finite-set theorems remain under visible `0 ∈ T`, and Exercise 8.39(b) remains core-proved. |
| `REVIEW_EVIDENCE_LIMITATION` | V7-F2, V7-F3, V7-F4, V7-F5 | 3 confirmed + 1 revised | **HISTORICAL EVIDENCE GAP, CLOSED.** The earlier review left 69 rows without accepted citation or witness evidence. The completed Round 9 V7 register subsequently gave every load-bearing row positive citation or compiled-witness evidence and left zero `UNVERIFIED_SANITY` or unreviewed rows. |
| `RESOLVED_AS_NONDEFECT` | V1-F2, V8-F2 | 2 revised | Repeated warning headers are bounded maintenance observations, not distinct semantic defects. |
| `NO_CHANGE` | V9-F7 | 1 rejected | The controlling task explicitly permits the printed `lake env lean` command form, and the referenced file compiles; the alleged command defect was a false positive. |

Thus the historical split was **8 fixed / 9 frozen blockers / 1 Chevet source
limitation now resolved by removal / 4 review-evidence limitations / 2
nondefects / 1 rejected with no change**. No historical ID was silently
dropped.

## Historical pre-removal V1--V10 soundness-finding dispositions

Before the 2026-07-20 scope removal, the post-restructuring reports contained
14 findings: **0 Critical / 0 Major / 3 Minor / 11 Info**. Their
final-correction validation is preserved here as provenance. The active
post-removal V1--V10 counts and verdicts are reported in
`Verification/README.md`; this historical table is not a current census.

| Stable ID | Verdict | Resolution |
|---|---|---|
| V1-F1 | REVISED | Successful-build warning instances are maintenance evidence, not distinct mathematical defects.  Retained and measured. |
| V8-F1 | CONFIRMED / FIXED IN ROUND 10 | The 166-row pre-removal package-lint population contained 97 confirmed missing-docstring defects. Scope removal eliminated the proposition-only-structure row; Round 10 then added all 97 missing declaration docstrings. The surviving 68 rows are INFO-only API/name/automation advisories. |
| V8-F2 | REVISED / DUPLICATE / INFO | Exact replayed-instance view of V1-F1; no second edit campaign. |
| V3-F1, V4-F1, V5-F1--F4, V7-F1--F3, V8-F3, V10-F1 | INFO | No action under the controlling rule: intentional Exercise debt, standard-only generated opacity, complete trust surfaces, positive definition evidence, complete lint coverage, and source-disclosed unpublished conditional infrastructure. |

The original V8-F1 row-level split is exact: **97 documentation rows + 48
unused-argument + 13 simplifier-normal-form + 4 declaration-form + 2 naming
+ 1 simplifier-commutativity + 1 proposition-only-structure = 166**.  The
proposition-only-structure row disappeared with scope removal, and the 97
documentation rows were genuinely fixed in Round 10. The 68 retained rows do
not authorize renaming, signature weakening, reducibility changes, simp-set
changes, or edits to vendored MatrixConcentration code.

## Active Round 10 soundness overlay

The active ten-report population is **0 Critical / 0 Major / 0 Minor / 14
Info**. V1-F1 is an informational build-warning-instance boundary. V8-F1 and
V8-F2 are informational after the documentation repair and duplicate-instance
adjudication; V8-F3 remains the positive coverage statement. V3-F1, V4-F1,
V5-F1--F4, V7-F1--F3, and V10-F1 are the unchanged ledgered boundaries and
positive-assurance rows. V2, V6, and V9 have no finding. No active finding
authorizes or requires a further Lean correction.

## Round 11 layout-only overlay

Round 11 reorganizes project records and physical Exercise module paths; it
does not change a book statement, declaration namespace, signature, or proof
body. Exactly 67 Lean files moved from `ChapterN/Exercise` into the single
`Exercise/ChapterN` tree. The nine root imports and the imports internal to
the moved tree now use `HighDimensionalProbability.Exercise.ChapterN`, while
public declaration namespaces such as `HDP.ChapterN.Exercise` remain stable.

The [all-source delta certificate](logs/exercise_reorganization_delta.log)
binds Round 10 digest
`bca641bd4c523754aa472b97cb1ed5638a6eb7361f99158a3f231a03a7446460`
to current digest
`78da8753a3367be0ae4c72df049a99f33723a7b22a1d08384714cc59d08853d4`.
It proves 222→222 library files, 67 exact moves, 52 byte-identical moved
files, 68 forced moved-file import rewrites, nine root-import rewrites, four
path-only comment rewrites, and zero unexpected or declaration-level source
change. The reorganized 8,670-job root target, its fixed-point replay, and the
8,701-job isolated Appendix target all completed with exit 0 before fresh
environment evidence collection began.

The source root now contains only `README.md`, `APPENDIX_SUMMARY.md`, and
`HUMAN_VERIFICATION_LOG.md`. Current numbered reports and correction records
live under `Verification/`; five immutable predecessor records live under
`Verification/archive/`. Historical baseline paths remain historical
identities. At the owner's request, regeneration of live `current_file`,
module, census, review, and build records is deferred until the additional
requested changes are applied; the partially collected Round-11 V4 shard was
neither merged nor installed.

## Dependency-cone and proof audit

- F-01/F-02/F-06 stay inside the Chapter 3 Ginibre/GOE block and its
  publication records. The audit covered coordinate laws and independence,
  symmetric support, concrete symmetrization, conjugation, and Exercises
  3.18--3.20.
- F-04 reaches Chapter 7's extended-expectation definitions and bridges, the
  downstream Sudakov development (approximately lines 9,960--10,697 at audit
  time), and Appendix Brownian-reflection references.
- F-05 reaches Chapter 8's extended population risk, finite bridge and core
  engines (approximately lines 17,304--18,199), plus
  `Exercise/Chapter8/Sec04.lean:204--266`. `labeledPopulationRisk` is
  unrelated.
- F-07--F-09 are additive: existing raw scalar/isotropy/vector APIs retain
  their types. The former Positive-Ricci and Borell Appendix consumers were
  rechecked during Round 9 and then deliberately removed on 2026-07-20; the
  reusable raw APIs and Borell domain-support declarations remain.
- F-10 has exactly four reference sites: the `HasGaussianVectorLaw`
  definition, its Chapter 3 affine equivalence,
  `Exercise/Chapter3/Sec04.lean:78`, and
  `Exercise/Chapter6/Sec02.lean:117`. The last two are intentional
  category-A exercise leaves; their statements, not their placeholder proofs,
  were rechecked for PSD compatibility.

The corrected-endpoint and Appendix axiom audits contain no nonstandard
axiom.  Static reconciliation finds exactly 228 executable `sorry` proofs,
all in the intentionally deferred non-load-bearing exercise leaves; Appendix
source has zero `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide`
proof constructs.

Pass 07 added 100 core commands (91 target kinds: 64 theorems, 4 lemmas, and
23 definitions) and 2 Appendix target declarations. In that historical pass
it removed and renamed no declaration. The machine-checkable evidence is the
[added-command register](inventory/pass07_declaration_changes.tsv),
[23-row same-name register](inventory/pass07_same_name_changes.tsv),
and [summary](inventory/pass07_declaration_changes_summary.json);
the [declaration-log checker](scripts/pass07_declaration_change_log.py).
After the 2026-07-20 removal overlay, the active consolidated core census is
2,862 theorems, 1,608 lemmas, and 1,155 definitions (5,625 total); the broader
documentation audit covers all 6,073 non-Appendix target declarations in 101
files with zero issues. The historical Pass 07 population and its authenticated
`baseline_file` locations remain frozen as provenance. Its live `current_file`,
line, file-hash, module, and source-manifest fields are projected through the
exact later 12-declaration removal ledger and the certified Exercise-tree
reorganization. The summary records the six removed core commands and two
retained finite-Chevet interface changes as a separate post-Pass-07 overlay;
they are not silently recounted as Pass 07 additions, removals, or same-name
changes.

The frozen post-restructuring, pre-removal Round 9 V4 environment was
complete:
**225/225 modules**,
**15,052 declaration/type rows**, **81,067 binder rows**, and **1,450,620
direct dependency edges**.  It finds exactly 228 exercise `sorryAx`
declarations, zero Appendix `sorryAx`, and zero nonstandard non-`sorry`
axioms. The former Round 8 shard/source-delta records remain historical
provenance. V7 independently reported positive evidence for all **273/273**
load-bearing definitions in that frozen pre-removal environment.

After the two module deletions, the Round-9 active source manifest
authenticated **226 entries** with digest
`83678e994eecf416759cb099d5e69f9d03c15921960d4f3b69d055a7a9e8fe27`.
Round 10's 97 declaration docstrings changed that digest to
`bca641bd4c523754aa472b97cb1ed5638a6eb7361f99158a3f231a03a7446460`.
Round 11's certified Exercise-tree move changed the intermediate tree to
`78da8753a3367be0ae4c72df049a99f33723a7b22a1d08384714cc59d08853d4`.
A fresh V4 collection was started at that digest and then intentionally
stopped before merge/install when the owner requested additional changes.
After those changes, V4/V7 and all downstream current figures must be
regenerated together; the installer has no earlier-digest fallback and must
not relabel Round-9, Round-10, or partial Round-11 evidence. The 225-module
figures above remain explicitly historical.

## Row-level evidence closure

Three generated records make the dependency and faithfulness claims
row-addressable: the
[five-row historical `PARTIAL` overlay](inventory/pass07_core_partial_resolutions.tsv),
the [11-row Round 5 PDF replay](review/pass07_round5_pdf_faithfulness.tsv),
and the [dependency-cone ledger](inventory/pass07_dependency_cones.tsv).
The [fail-closed evidence gate](scripts/pass07_evidence_gate.py)
reconstructs those artifacts and rejects drift. It requires exactly the five
historical overlay rows and 11 PDF obligations, checks the complete declared
dependency closures, and binds every accepted row to the current source
manifest, authoritative PDF, declaration types, and axiom evidence by hash.
It also rejects nonstandard axioms, `sorryAx` on required proved endpoints,
and any `sorryAx` on an Appendix member admitted to the evidence set; the
Appendix-wide placeholder audit remains zero.

## Round 8 clarification and replay — 2026-07-19

The following is historical pre-removal provenance. Round 8 rechecked the
owner-selected outcomes without broadening them. Q1 then
records the correct proof provenance: the book's Sudakov--Fernique hint is
sound, and only the attempted scalar outer-radius comparator fails. Q2 now
records that the certificate encodes `Ric ≥ κg`, exposes `Measurable f` and
`Integrable f μ`, and covers all `L ≥ 0` through a separately proved zero
branch. Q3 remains deliberately skipped, while Q4 remains fully and
source-faithfully proved. The synchronized source passed the **8,670-job
whole build**, the **8,703-job isolated Appendix build**, and the
**20-endpoint axiom replay** with only the standard allowed axioms and no
`sorryAx`.  It then passed the fresh two-shard V4 generation and exact merge,
the expected analyzer exit 2 for the four-module frozen boundary, the
aggregate V4 static gate, and the atomic completion check. Round 7 remains
pre-rerun provenance; Round 8 was authoritative for that historical layout
and is superseded by Round 9.

## Appendix owner-selected outcomes

| Scope item | Book item | Current outcome |
|---|---|---|
| Q1 | **Book Exercise 8.39(a)** and **Book Remark 8.6.3**, physical 268/260 and 260/252 | **RESOLVED BY REMOVAL (2026-07-20).** The arbitrary-set class, five conditional consumers, and Appendix wrapper/module were deleted. The direct finite-set theorems remain under explicit `0 ∈ T`; Exercise 8.39(b) remains core-proved. |
| Q2 | **Book equation (5.8)**, physical 156 / printed 148 | **RESOLVED BY REMOVAL (2026-07-20).** The assumption-strengthened module and its three theorems were deleted; the reusable Bakry--Émery infrastructure remains. |
| Q3 | **Book Example 3.4.6**, physical 83–84 / printed 75–76 | **RESOLVED BY REMOVAL (2026-07-20).** The Borell principle and conditional specialization were deleted. Five unconditional convex-body domain declarations remain as support infrastructure, not a marginal-tail or `ψ₁` claim. |
| Q4 | **Book Remark 7.2.1**, physical 207 / printed 199 | SOURCE-FAITHFUL PROVED by finite-grid reflection, layer cake, and a vanishing mesh error. |

The immutable census artifact remains 838 rows. Its active projection is
**835 = 769 core + 66 Appendix proved + 0 deferred/source-limited**. The
separate active registry is **14/14 source-faithful proved**; its 15 direct
Appendix imports include the non-target Borell domain-support module.

The exact active-census overlay removes
`census-bf1de680f35b52dc`, `census-628be74004e48217`, and
`census-939078c2ac4f78a5`; reframes
`census-8e50e84b6b82a573` as core-proved Exercise 8.39(b); and retains the
Round 9 Brownian move `census-360c40946511e7a9` to Appendix-proved. The
611-row public correspondence contains none of the removed scope rows and is
unchanged.

## Historical correction ledger (Passes 04–05)

| Book item | Input class | Verdict | Evidence and action |
|---|---:|---|---|
| Theorem 0.0.2 | missing | confirmed | PDF pp. 2–3 states the equal-weight `1/sqrt(k)` approximation. Added `HDP.Chapter0.approximate_caratheodory`. |
| Corollary 0.0.3 | missing | confirmed | PDF pp. 3–4 constructs at most `N^k` empirical-average centers. Added `HDP.Chapter0.exists_polytope_cover`. |
| (0.3) | missing | confirmed | PDF p. 4 gives `Vol(P)/Vol(B) <= N^k/k^(n/2)`. Added the division-free equivalent `HDP.Chapter0.polytope_volume_equation_0_3`. |
| (0.4) | missing | confirmed | PDF p. 4 gives `k₀=n/(2 log N)`. Added the critical-point equation and uniqueness declarations. |
| Exercises 0.1(a), 0.2, 0.3 | missing/partial | confirmed, load-bearing | PDF proof of Theorem 0.0.2 explicitly invokes 0.1(a) and 0.3; the vector 0.2 statement was genuinely absent. Added three proved vector results. |
| Theorem 0.0.4; Remark 0.0.5 | missing | confirmed-fixed | Added the exact `(3√(log N/n))^n` relative-volume theorem, with `k=⌈n/(2 log N)⌉`, all small/large and `N=0,1` branches, plus the precise `log N_n/n→0` radius and volume-coefficient limits. All five public endpoints were axiom-audited. |
| §1.6 Markov optimality | missing | confirmed | PDF p. 16 asserts best possible from the mean alone. Added an extremizing two-point PMF, `markov_inequality_is_sharp`. |
| Chapter 1 notes, Robbins bounds | missing | fixed | `factorial_robbins_two_sided` proves both sharp exponential remainder endpoints globally for positive `n`. |
| Question 2.1.1; (2.1) | partial | confirmed | PDF asks for the exact fair-coin Chebyshev calculation. Added `fair_coin_chebyshev_equation_2_1`. |
| (2.2) | unsure | rejected | The PDF explicitly labels the moving-threshold CLT substitution as unjustified; it is a heuristic, not a theorem conclusion. |
| Remark 2.1.3 | unsure | rejected | It only directs the reader to non-load-bearing Exercise 2.3; no main-text endpoint is asserted. |
| Remark 2.2.3 | unsure | rejected | Methodological prose (“non-asymptotic”), not a mathematical proposition. |
| Example 2.6.5 negative list | partial | revised | The missing negative examples are assigned to non-load-bearing Exercise 2.25; retain the proved main-text positive examples and reject exercise completion under project policy. |
| Remarks 2.7.2 / Exercises 2.33–2.34 | missing | rejected | The asserted reverse-bound checks are delegated entirely to non-load-bearing exercises. |
| Remark 2.8.2 | unsure | rejected | Explicit Taylor heuristic without a quantified remainder statement. |
| Chapter 3 covariance prose | partial | confirmed | PDF gives `Cov(X)=E[XXᵀ]-(EX)(EX)ᵀ` and the zero-mean specialization. Added both exact matrix identities. |
| Example 4.1.5 | partial | confirmed | The source describes `UU^T` for an orthonormal-column matrix as the rank-`k` orthogonal projection. Added one theorem proving symmetry, idempotence, exact rank, identity on the column space, and vanishing on its orthogonal complement. |
| Chapter 7 Examples 7.1.2–7.1.5 | missing | rejected | Terminological/explanatory examples; the source states no theorem beyond the existing definition `RandomProcess = T → Ω → ℝ`. |
| Chapter 8 ψ₂ increment metric | missing | confirmed | PDF states the tautological metric observation. Added constant-one and existential wrappers. |
| Remark 8.2.4 | partial | confirmed | The finite-grid existence result did not cover the source's full Lipschitz class. Added `remark_8_2_4_exists_good_lipschitz_sample`, obtained from the measurable arbitrary-class expectation bound by Markov's argument. |
| Remark 9.6.5 | missing | rejected | The PDF explicitly identifies an open problem; documenting it is faithful and no theorem/axiom should be invented. |
| Remarks 2.3.3 and 2.3.5 | partial | rejected | Qualitative comparison and plotting intuition; Chernoff bounds, Poisson asymptotics, and both deviation regimes already give the mathematical content. |
| §2.4 median robustness prose | missing | confirmed-fixed | Added `median_one_coordinate_robust`: after replacing one coordinate, any median of the contaminated sample retains all but at most one lower- and upper-half rank witness in the original sample. This is the cardinal form of the PDF's “stays put or just shifts … at most to the next point.” |
| Example 2.8.7 | partial | revised | Generic implications and the exponential example are covered; the remaining named-law classifications are assigned to non-load-bearing Exercise 2.39. |
| Remark 2.9.3 | partial | rejected | The proved two-regime Bernstein tail and exponential-law obstruction already imply the stated necessity; the remark adds interpretation only. |
| Corollary 3.2.3 | partial | confirmed-fixed | Added the exact covariance-operator quadratic-form/variance identity and the ordered covariance PCA maximum principle for arbitrary square-integrable random vectors. |
| Remark 3.2.4 | unsure | rejected | Practical guidance with no asserted error bound or mathematical endpoint. |
| Corollary 3.3.3 | partial | confirmed | Added `sum_independent_gaussians_parameters`, exposing Gaussian closure together with the exact summed scalar mean and variance. |
| Definition 3.3.4 | partial | confirmed-fixed | Added arbitrary rectangular affine Gaussian measures, proved their covariance law `AAᵀ`, and established equivalence with `HasGaussianVectorLaw` for positive-semidefinite covariance. |
| Equation (3.14) | partial | confirmed-fixed | Added and consolidated-module-verified the exact `1/n` squared-inner-product expectation and the normalized Markov tail `P{|⟨X,Y⟩|≥C/√n}≤1/C²`. |
| Equations (3.17) and (3.18) | unsure/partial | rejected | (3.17) is explicitly informal; (3.18) is a proof decomposition, while Lean already proves the final uniform projective CLT. |
| Theorem 3.4.5; (3.19) | partial | confirmed-fixed | Replaced the coarse tail with the exact PDF bound `P{⟨X,v⟩ ≥ t} ≤ 2 exp(-n t²/2)` for every `t ≥ 0`, including the endpoint branches, and derived the stated subgaussian-vector conclusions. The proof exposes the normalized-Gaussian reduction and the Laplace/product identities from (3.20)–(3.21). |
| Equations (3.20)–(3.21) | missing | rejected | Proof-local identities for one route to Theorem 3.4.5, not separate conclusions. |
| Example 3.4.6 | partial | removed from active coverage | The bounded-body conclusion remains covered and the PDF's unscaled isotropic-cube sentence requires `sqrt(3)` scaling under Definition 3.2.5. The former universal Borell proposition and conditional specialization were removed on 2026-07-20; the retained module supplies domain facts only. |
| Examples 3.4.7–3.4.8 | missing | confirmed-fixed | Added the exact coordinate-distribution vector `ψ₂` norm `√(n/log(n+1))` (and the unscaled-basis value `1/√log(n+1)`), together with the finite isotropic subgaussian entropy bound `n/K²-log 2` and support bound `(1/2)exp(n/K²)`. The former exercise-only placeholders were removed. |
| Equation (3.25) | missing | rejected | Proof-local truncation estimate for a route superseded by the stronger compiled Krivine proof. |
| Equation (3.31) | partial | confirmed-fixed | Added `graphCutObjective_eq_cutValue`, proving by the crossing-graph degree-sum formula that the adjacency-matrix sign objective is exactly the cut cardinality. |
| Equations (3.32)–(3.33), Proposition 3.6.3, Theorem 3.6.4 | partial | confirmed-fixed | Added an attained graph SDP value, exact graph maximum characterization, `maxcut(G) ≤ sdp(G)`, an actual random-cut cardinality theorem, and the graph-level `439/500` Goemans--Williamson guarantee against both optima. |
| Definition 3.7.1; (3.36) | partial | confirmed-fixed | Added `TensorSpace` for independently sized dependent finite axes, the coordinate sum `tensorInner`, its equality with the ambient Euclidean inner product, and the proof that `TensorPowerSpace` is the equal-axis specialization. |
| Example 3.7.2 | partial | rejected | Vector and matrix cases are definitional specializations; a naming-only wrapper adds no mathematical content. |
| Lemma 3.7.7 | partial | confirmed-fixed | Added `absolutePowerSummable_of_entire`, proving absolute convergence at every radius from pointwise convergence of the real power series by geometric domination at twice the radius, and exposed the literal-hypothesis feature-map wrapper `realAnalytic_featureMap_of_entire`. |
| Remark 3.7.9 | partial | rejected | Expected-value rounding is already compiled inside the public theorem's proof; the remark is algorithmic interpretation. |
| Equation (3.38); Moore–Aronszajn prose | partial | confirmed-fixed | Added `scalarKernel_featureMap_iff_posSemidef`. Sufficiency embeds a scalar PSD kernel into Mathlib's operator-valued RKHS construction; necessity proves directly that every (possibly infinitely indexed) feature Gram kernel is PSD. |
| Chapter 3 historical/optimality notes | missing/unsure | rejected | Later optimal constants, best-known algorithms, UGC hardness, and state-of-knowledge claims are bibliographic context, not fixed probability conclusions. |
| Notes improving Exercise 3.13 | partial | rejected | This is a notes-only sharpening of non-load-bearing Exercise 3.13, not a main-line endpoint; the exercise policy intentionally excludes its sharp-constant completion. |
| Notes on PSD Grothendieck; Exercise 3.55 | missing/partial | rejected | Non-load-bearing practice-exercise completion, outside policy. |
| Remark 4.1.3; Equation (4.4) | partial | confirmed-fixed | Added orthonormal-basis extensions, square orthogonal column matrices, the rectangular singular-value diagonal, and the literal factorization `A = UΣVᵀ`. |
| Remark 4.1.9 | partial | confirmed-fixed | Added finite-dimensional attainment on the primal unit ball and an exact `IsGreatest` theorem for the primal/conjugate-dual bilinear values, including the `1` and `∞` endpoints. |
| Remark 4.2.13 | partial | revised | Random construction is proved; lattice construction is delegated to a non-load-bearing exercise. |
| Equation (4.31); Exercise 4.18 | partial | rejected | Non-load-bearing exercise conclusions; main-text norm definition and inequalities are covered. |
| Definition 5.1.1 | partial | confirmed | Added the extended least constant `lipschitzSeminorm` and proved `lipschitzSeminorm_le_iff`. The PDF's unrestricted differentiable-implies-Lipschitz sentence is false, so the existing bounded-derivative correction remains. |
| Example 5.1.2 | partial | confirmed | Exact constants are a numbered main-text example. Added proved core declarations `example_5_1_2a`, `example_5_1_2b`, and `example_5_1_2c`; the deferred exercise files are no longer the only evidence. |
| Remark 5.4.6 | partial | confirmed-fixed | Added explicit positive-semidefinite `2×2` matrices `A ≤ B` for which `B²-A²` has determinant `-1`, proving that the increasing scalar square function does not preserve Loewner order without commutation. |
| Equation (5.2) | missing | deferred-to-appendix-session | Specialization of spherical isoperimetry, whose authoritative theorem is in the off-limits appendix subtree. |
| Equation (5.3) | missing | fixed | `sphericalCapBand_subset_neighborhood` proves the full-dimensional hemisphere-neighborhood containment using normalized equatorial projection, including the polar case. |
| pp. 145–146 median existence | missing | confirmed-fixed | Added `exists_measureMedian` by the CDF lower-quantile construction and `exists_isMedian` by pushforward, covering arbitrary a.e.-measurable real random variables including atomic laws. |
| p. 163 noncommuting exponentials | missing | confirmed-fixed | Added explicit symmetric `2×2` matrices, computed both individual exponentials by diagonalization, and proved their product is non-Hermitian while the exponential of the sum is Hermitian. |
| Remark 6.5.2 | partial/missing | revised | Rectangular/noisy extensions and log-free/exact-recovery prose have no uniquely specified hypotheses or target theorem in the PDF. |
| Exercises 6.31–6.32 | unsure | rejected | Non-load-bearing “state and prove a version” prompts with no unique target. |
| Example 7.1.6 | missing | confirmed-fixed | Added the exact Brownian and independent centered unit-variance random-walk identities `brownian_processIncrement` and `randomWalk_processIncrement`. |
| Theorem 7.1.11 | partial | confirmed-fixed | Added the affine canonical representation of an arbitrary finite Gaussian process, proved coefficient norms equal marginal standard deviations, and transported the centered-maximum `SubGaussian` and `ψ₂` conclusions back to the original probability space. |
| Proposition 7.5.2 | partial | confirmed-fixed | Completed the actual arbitrary-set interface: finiteness exactly on bounded sets; translation and orthogonal invariance; convex-hull, Minkowski-sum, scaling, and symmetrization identities; the source two-sided diameter bounds; and the continuous-linear-image bound. Extended-valued statements are paired with bounded safe-real wrappers, and all public endpoints were axiom-audited. |
| Example 7.5.8; Equation (7.19) | partial | fixed | `crossPolytopeGaussianWidth_asymptotic_actual` transports the iid asymptotic to the canonical widths, and `crossPolytopeGaussianWidth_twoSided` packages the direct finite comparison for every `n ≥ 2`. |
| Remark 7.5.10 | missing | rejected | Qualitative synthesis without a single quantified comparison. |
| Equation (7.21) | partial | confirmed | Added `orthogonalProjection_unitBall_diam`: the image is exactly the subspace unit ball and has diameter two. |
| Remark 7.2.1 Brownian reflection formula | missing | confirmed-fixed | The exact finite-subfamily expected-supremum endpoint is now proved by finite-grid reflection, layer cake, and a vanishing mesh error. Exercise 7.2 is an unrelated symmetrization exercise and is not the proof assignment for this formula. |
| Example 8.1.2, arbitrary Gaussian process | partial | confirmed-fixed | Proved a noncentered scalar Gaussian `ψ₂`-to-`L²` bound and applied it to every increment of an arbitrary Gaussian process, with an explicit universal constant and no finiteness assumption on the index set. |
| §9.2.3 ellipsoid identities | partial | revised-fixed | Added the actual covariance ellipsoid, its exact radius/operator-norm identity, and the arbitrary-set Gaussian-complexity-envelope bound by `‖B‖_F = √tr(BᵀB)`. |

Every historical result listed as proved passed its recorded module and axiom
audit. Pass 07 edited core exactly as recorded in this ledger and touched the
isolated Appendix only at the four owner-selected Q1--Q4 boundaries described
above; no vendored dependency was edited.
