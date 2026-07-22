# Final correction report

Date: 2026-07-21  
Scope: Roman Vershynin, *High-Dimensional Probability*, second edition

> **Round 11 status:** the certified Exercise/record reorganization is applied,
> but its full V1--V10 replay is intentionally deferred pending additional
> owner-requested changes. The partial fresh V4 shard was stopped before
> merge/install and is not evidence. Completed verdicts below therefore remain
> the Round-10 baseline until the combined replay is run.

## 1. Authoritative disposition

This is the active post-removal record of the Pass 07 correction and final
V1--V10 re-certification. It supersedes present-tense claims in the historical
Pass 05, Pass 06, and Round 1--9 records while preserving those records as
provenance.

Pass 07 validated the 14 Pass 05 findings as **9 CONFIRMED, 4 REVISED, and 1
REJECTED**. Every actionable core defect was corrected, all five former core
`PARTIAL` rows were completed, and no in-scope `MISSING` row remained. The 25
non-INFO findings in the historical Pass 06 bundle were independently
classified as **10 CONFIRMED, 14 REVISED, and 1 REJECTED**. The active
post-removal V1--V10 bundle contains **0 Critical, 0 Major, 0 Minor, and 14
Info** findings.

Three non-source-faithful theorem families were ultimately removed rather
than counted as book coverage:

- the arbitrary-set Gaussian--Chevet upper-principle family;
- positive-Ricci concentration statements conditional on an explicit
  `RiemannianDiffusionLaw`; and
- the universal Borell convex-body `ψ₁` principle and its conditional
  specialization.

The scope removal deleted exactly **12 declarations and 2 Lean files**. It
did not weaken or remove the finite Gaussian--Chevet results, Exercise
8.39(b), unconditional convex-body domain support, reusable Bakry--Émery
infrastructure, `RiemannianDiffusionLaw`, or the independently discharged
Special Orthogonal and Grassmannian concentration routes.

No `MatrixConcentration` source file was changed by the correction or the
scope removal. The active project still contains exactly the same ten
MatrixConcentration modules. The toolchain selector, Lake package definition,
dependency lockfile, and pinned dependencies were also unchanged.

## 2. Finding validation and correction outcomes

### 2.1 Pass 05 findings

| ID | Validation | Final outcome |
|---|---|---|
| F-01 | CONFIRMED | Replaced the rigged GOE interface with independent-entry GOE data, concrete Ginibre symmetrization, and orthogonal-conjugation invariance. |
| F-02 | CONFIRMED | Proved the concrete `Gu,Gv` laws and independence from one Ginibre matrix. |
| F-03 | CONFIRMED; final scope revised | Removed the assumption-strengthened equation-(5.8) source interface and its three theorems; reusable diffusion infrastructure remains. |
| F-04 | CONFIRMED | Added extended expectation and rebuilt arbitrary finite-subfamily expected supremum; the Brownian reflection endpoint is proved. |
| F-05 | CONFIRMED | Changed population risk to `ℝ≥0∞`, added a proof-carrying finite bridge, and repaired downstream minimizer and learning engines. |
| F-06 | CONFIRMED | Added concrete left/right Ginibre actions and proved their invariant laws. |
| F-07 | REVISED | Retained the generalized raw analytic helpers and added source-facing bundled subgaussian/subexponential random-variable predicates and bridges. |
| F-08 | REVISED | Retained raw isotropy and added the probability, measurability, and `MemLp 2` random-vector bundle. |
| F-09 | REVISED | Retained the raw supremum helper and proved finite-dimensional vector-`ψ₂` boundedness for the source-facing bundle. |
| F-10 | CONFIRMED | Added positive-semidefinite covariance to `HasGaussianVectorLaw` and re-audited its complete dependency cone. |
| F-11 | REVISED | Added an extended MGF and documented the finite real helpers' exact domains. |
| F-12 | CONFIRMED, already actioned | Revalidated the arbitrary-index equation-(7.14) mapping after the F-04 repair. |
| F-13 | CONFIRMED, already actioned | Revalidated the arbitrary-set Theorem-7.6.1 mapping. |
| F-14 | REJECTED / STRONGER | The documented zero-denominator extension of conditional probability changes no positive-domain theorem; no edit was warranted. |

The only rejected Pass 05 finding is F-14. The dependency-cone review covered
the Chapter 3 GOE/Ginibre block, Chapter 7 extended-expectation and
Sudakov/Brownian consumers, Chapter 8 risk engines and exercise consumers,
every reference to `HasGaussianVectorLaw`, and the source-facing
subgaussian, subexponential, isotropy, vector-`ψ₂`, and MGF wrappers.

### 2.2 Historical Pass 06 findings

The historical 25-row non-INFO population has the following exhaustive
disposition:

| Final state | Rows | Accounting |
|---|---:|---|
| Fixed editable defects | 8 | Seven CONFIRMED and one REVISED |
| Former frozen-layout blocker views | 9 | Nine REVISED; the current layout has no such subtree, orphan, or missing module |
| Resolved by removal | 1 | One REVISED arbitrary-set Chevet limitation |
| Historical V7 evidence gaps, now closed | 4 | Three CONFIRMED and one REVISED |
| Warning-count observations resolved as nondefects | 2 | Two REVISED |
| No change | 1 | One REJECTED (`V9-F7`) |
| **Total** | **25** | **10 CONFIRMED / 14 REVISED / 1 REJECTED** |

`V9-F7` is the only rejected historical soundness finding: the controlling
task explicitly permits the printed `lake env lean` command form, and the
referenced file compiles.

### 2.3 Correction volume and proof closure

The correction phase added **100 core commands**, of which **91** were target
kinds (**64 theorems, 4 lemmas, and 23 definitions**), plus **2 Appendix
target declarations**. It recorded **23 same-name signature or body changes**
and no rename. That frozen correction register predates the later deliberate
12-declaration/2-file scope removal and remains historical rather than being
rewritten.

All corrected, added, and retained Appendix endpoints in the recorded axiom
harnesses use only `propext`, `Classical.choice`, and `Quot.sound`. No hidden
`sorry`, `admit`, custom axiom, `native_decide`, or `unsafe` construct was
introduced. The only current `sorryAx` population is the 228 intentional
Exercise leaves described below.

## 3. Exact removed and retained source surface

The two deleted files are:

- `HighDimensionalProbability/Appendix/GaussianChevet.lean`;
- `HighDimensionalProbability/Appendix/PositiveRicciConcentration.lean`.

The twelve deleted declarations are:

1. `HDP.Chapter3.BorellConvexBodyPsiOnePrinciple`
2. `HDP.Chapter3.convexBodyUniform_marginal_subExponential_of_borell`
3. `HDP.Chapter5.positive_ricci_concentration`
4. `HDP.Chapter5.positive_ricci_concentration_psi2`
5. `HDP.Chapter5.positive_ricci_concentration_psi2_of_lipschitz`
6. `HDP.Chapter8.GaussianChevetUpperPrinciple`
7. `HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary_envelope`
8. `HDP.Chapter8.gaussianChevetExpectationEnvelope_ne_top_of_isBounded`
9. `HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary_envelope`
10. `HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary`
11. `HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary`
12. `HDP.Chapter8.gaussianChevetUpperPrinciple_external`

The retained boundary is exact:

- `HDP.Chapter8.exercise_8_39a_gaussian_chevet` and
  `HDP.Chapter8.remark_8_6_3_gaussian_chevet` remain finite-set results with
  the visible hypothesis `hzero : 0 ∈ T`;
- `HDP.Chapter8.exercise_8_39b_gaussian_chevet_reverse_arbitrary` remains
  proved;
- `Appendix/BorellConvexBody.lean` retains exactly five unconditional
  normalized-law/domain-support declarations and no marginal-tail or `ψ₁`
  principle; and
- `RiemannianDiffusionLaw`, reusable Bakry--Émery infrastructure, and the
  Special Orthogonal and Grassmannian routes remain available.

### 3.1 Exact active counts

| Measurement | Active value |
|---|---:|
| Physical library files | **222 = 212 HDP + 10 MatrixConcentration** |
| Environment graph nodes, including the HDP root | **223** |
| Authenticated source-manifest entries | **226** |
| Active PDF-revalidated conclusions | **835 = 769 core + 66 Appendix + 0 deferred/source-limited** |
| Publication-map rows / unique endpoints | **611 / 540** |
| Consolidated target-kind declarations | **5,625** |
| Documented non-Appendix target declarations | **6,073 / 6,073 in 101 files** |
| Ledgered Exercise `sorry` proofs | **228 in 46 files** |
| Active Appendix registry | **14/14 source-faithful proved targets** |
| Appendix aggregator direct imports | **15** |

## 4. Exact structural and publication deltas

The immediate comparison baseline in this section is the complete
post-restructuring, pre-removal Round 9 tree. Values are not inferred when no
like-for-like baseline artifact exists.

### 4.1 Source, graph, and manifest

| Measurement | Before removal | Active after removal |
|---|---:|---:|
| Physical library files | 224 | **222** |
| HDP physical files | 214 | **212** |
| MatrixConcentration physical files | 10 | **10** |
| Environment graph nodes, including the HDP root | 225 | **223** |
| Syntactic imports | 916 | **911** |
| Resolved local import edges | 434 | **429** |
| External import references | 482 | **482** |
| HDP-root-reachable physical files | 111 | **111** |
| Appendix closure, including shared dependencies | 146 | **144** |
| Shared root/Appendix dependencies | 33 | **33** |
| Appendix-only physical files | 113 | **111** |
| Orphan physical files | 0 | **0** |
| Authenticated manifest entries | 228 | **226** |
| Manifest digest | `cf7962dd80427c59c75b1dcc111f654ab9a53d2dba0ccadd7baf840af542c01d` | **`78da8753a3367be0ae4c72df049a99f33723a7b22a1d08384714cc59d08853d4`** |

The active 226-entry manifest consists of 222 physical library files, the
root aggregator, and the three unchanged Lake/toolchain pin files.
The immediately preceding post-removal digest was
`83678e994eecf416759cb099d5e69f9d03c15921960d4f3b69d055a7a9e8fe27`.
The Round-10 delta certificate compares every library file plus the root
aggregator and proves that the transition to the active digest adds exactly
97 one-line declaration docstrings in 25 files, replaces one blank line, and
has zero nonblank non-documentation source change, producing intermediate
digest
`bca641bd4c523754aa472b97cb1ed5638a6eb7361f99158a3f231a03a7446460`.
The Round-11
[Exercise reorganization certificate](logs/exercise_reorganization_delta.log)
then proves the exact path/import-only transition from that intermediate
digest to the active digest: 67 physical moves, 68 moved-file import
rewrites, nine root-import rewrites, four comment-only path updates, and zero
declaration namespace, statement, or proof-body change. Current V4 raw tables
were not installed at this intermediate digest: their fresh collection was
intentionally stopped before merge when the owner requested additional
changes. No former-digest or partial evidence is relabelled or accepted
through a fallback; the full replay must follow the additional changes.

### 4.2 Census, publication, declarations, documentation, and Appendix

| Measurement | Before removal | Active after removal |
|---|---:|---:|
| Valid PDF-revalidated conclusions | 838 | **835** |
| Core-formalized conclusions | 768 | **769** |
| Appendix-proved conclusions | 66 | **66** |
| Deferred/source-limited conclusions | 4 | **0** |
| Publication-map rows | 611 | **611** |
| Unique published endpoints | 540 | **540** |
| Consolidated target-kind declarations | 5,630 | **5,625** |
| Consolidated theorems | 2,867 | **2,862** |
| Consolidated lemmas | 1,608 | **1,608** |
| Consolidated definitions | 1,155 | **1,155** |
| Documented non-Appendix declarations | 6,078 | **6,073** |
| Documentation-audit files | 101 | **101** |
| Documentation-contract issues | 0 | **0** |
| Registered Appendix targets | 17 | **14** |
| Source-faithful registered targets | 14 | **14** |
| Assumption-strengthened registered targets | 2 | **0** |
| Skipped registered targets | 1 | **0** |
| Appendix aggregator direct imports | 17 | **15** |
| Appendix/repair axiom-harness endpoints | 20 | **15** |
| Ledgered Exercise `sorry` declarations | 228 | **228** |
| Exercise files containing those declarations | 46 | **46** |

The publication map is a curated correspondence, not the exhaustive
whole-book census. Its rows and endpoint set are unchanged because none of
the three removed census scopes was a publication-map row.

### 4.3 Pass 05 to active whole-book chapter census

The Pass 05 input had 873 rows: 838 valid conclusions and 35 rejected
non-conclusions. Its valid split was `763 core + 5 core partial + 65 Appendix
proved + 5 Appendix unresolved/deferred`. The final active split is `769 core
+ 66 Appendix proved + 0 deferred`, with three removed source scopes.

| Chapter | Pass 05 core | Pass 05 partial | Pass 05 Appendix proved | Pass 05 deferred | Rejected | Removed in final scope | Active core | Active Appendix | Active deferred | Active conclusions |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Appetizer | 11 | 0 | 0 | 0 | 0 | 0 | 11 | 0 | 0 | 11 |
| Chapter 1 | 62 | 0 | 1 | 0 | 0 | 0 | 62 | 1 | 0 | 63 |
| Chapter 2 | 70 | 0 | 1 | 0 | 8 | 0 | 70 | 1 | 0 | 71 |
| Chapter 3 | 93 | 3 | 0 | 1 | 14 | 1 | 96 | 0 | 0 | 96 |
| Chapter 4 | 117 | 0 | 0 | 0 | 3 | 0 | 117 | 0 | 0 | 117 |
| Chapter 5 | 99 | 0 | 12 | 1 | 0 | 1 | 99 | 12 | 0 | 111 |
| Chapter 6 | 47 | 0 | 0 | 0 | 4 | 0 | 47 | 0 | 0 | 47 |
| Chapter 7 | 80 | 1 | 0 | 1 | 5 | 0 | 81 | 1 | 0 | 82 |
| Chapter 8 | 112 | 1 | 8 | 2 | 0 | 1 | 114 | 8 | 0 | 122 |
| Chapter 9 | 72 | 0 | 43 | 0 | 1 | 0 | 72 | 43 | 0 | 115 |
| **Whole book** | **763** | **5** | **65** | **5** | **35** | **3** | **769** | **66** | **0** | **835** |

The arithmetic is exact: the historical input is
`873 = 763 + 5 + 65 + 5 + 35`, while the active projection is
`873 = 769 + 66 + 35 + 3` and `835 = 769 + 66`. All five former partial rows
(Exercises 3.18--3.20, Remark 7.2.1, and equation (8.37)) are complete. There
is no active in-scope partial or missing conclusion. The 191 wholly
non-load-bearing practice-exercise numbers remain outside this census.

### 4.4 Publication endpoint progression

| Stage | Correspondence rows | Verified / partial rows | Unique endpoints |
|---|---:|---:|---:|
| Pass 05 input | 611 | 609 / 2 | 534 |
| Corrected pre-removal tree | 611 | 611 / 0 | 540 |
| Active post-removal tree | 611 | 611 / 0 | 540 |

V9's current endpoint replay further partitions the 540 names into 527
project endpoints and 13 external Mathlib endpoints. Every project endpoint
is present in V4, no endpoint has a nonstandard axiom, and no README/V4 axiom
set differs.

### 4.5 Proofread-population progression

The frozen gap inventory contained **89 rows = 45 `PARTIAL` + 34 `MISSING`
+ 10 `UNSURE`**. PDF revalidation classified 51 as already faithfully
formalized, 35 as not separate in-scope conclusions, and 3 at the Appendix
boundary. The resulting Pass 05 audit had 14 findings and the 838-valid-row
split shown above; the final active tree has zero core partial, zero in-scope
missing, and zero deferred row.

Accordingly, the correction pass completed **5 confirmed `PARTIAL` rows** and
formalized **0 newly confirmed `MISSING` rows**: none of the 34 frozen
`MISSING` labels survived Pass-05 PDF validation as a separate absent in-scope
conclusion. This zero is a validation outcome, not an omitted work list. The
correction phase added declarations for validated defects and faithful
interfaces, but did not relabel any such addition as closure of a nonexistent
confirmed-`MISSING` row.

The sibling human-proofread register's active Section A scope is **496
applicable rows**. Two removed endpoint rows are no longer applicable, and
semantic rows S8--S10 record the three removed interface families as N.A.
Because the register is a human sign-off surface, its checkbox completion is
not inferred from the mechanical V1--V10 results.

## 5. Mechanical before-to-after ledger

### 5.1 V1 build and warning evidence

| Measurement | Pre-removal comparison | Active V1 replay |
|---|---:|---:|
| Combined/root build jobs | 8,670 | **8,671** |
| Isolated Appendix build jobs | 8,703 | **8,701** |
| Full-build warning instances | 1,918 | **1,915** |
| Appendix warning instances | 2,464 | **2,461** |
| Total warning instances | 4,382 | **4,376** |
| `sorry` warning instances | 228 | **228** |
| Non-`sorry` warning instances | 4,154 | **4,148** |
| Deprecation warning instances | 72 | **72** |
| Linter/style warning instances | 4,082 | **4,076** |
| `linter.style.longLine` instances | 1,898 | **1,892** |

The active combined HDP/MatrixConcentration build exited 0 in **3,573.196
seconds**; the isolated Appendix build exited 0 in **3,270.547 seconds**. The
job totals are replay/command measurements, not declaration counts. The
current combined command explicitly names both `HighDimensionalProbability`
and `MatrixConcentration`.

### 5.2 V3 and V5 source-trust surfaces

At the Pass 05 starting point, the source-token census was 229 executable
`sorry` occurrences: 228 Exercise leaves plus one Appendix target. The active
tree has **228**, all in the same 46 marked Exercise files, and Appendix has
zero. Across the immediate pre-removal to active comparison, the Exercise
population remains 228/46 and the Appendix population remains zero.
The active V3 lexical serialization contains **462 raw rows = 228 executable
`sorry` rows + 234 non-executable `EXERCISE-SORRY` marker rows**, and its
kernel join is exactly 228/228.

V5's active scan covers **222 files**, with **293 raw hits, 238 executable
hits, 55 non-code hits, and zero high-risk executable hit**. It classifies
**16 exported instances on Mathlib-owned carriers**. Its separate scratch
surface remains **46 files = 9 `tmp` + 36 `.audit_work/verification` + 1
legacy `.audit_work/READMEProvedAxioms.lean`**, with
238 raw and 125 executable hits, all classified. The like-for-like immediate
pre-removal V5 hit totals were not retained as a separate summary, so none is
invented; the measured physical-file delta is 224 to 222, while scratch and
the 16 exported instances are unchanged.

### 5.3 V4 exhaustive environment

| Measurement | Pre-removal V4 | Active V4 |
|---|---:|---:|
| Environment modules | 225 | **223** |
| Project declarations/type rows | 15,052 | **15,022** |
| Private declarations | 1,613 | **1,613** |
| Internal declarations | 4,964 | **4,955** |
| Telescope binder rows | 81,067 | **80,919** |
| Direct type/value dependency edges | 1,450,620 | **1,448,224** |
| Theorems | 12,687 | **12,668** |
| Definitions | 2,259 | **2,251** |
| Constructors / inductives / recursors | 35 / 35 / 35 | **34 / 34 / 34** |
| Internal opaque wrappers | 1 | **1** |
| `sorryAx` declarations | 228 | **228** |
| Project axiom declarations | 0 | **0** |
| Nonstandard non-`sorry` axiom declarations | 0 | **0** |

The active V4 collection is the validated sequential two-shard replay. Its
sole opaque row is Lean's internal wrapper for
`irreducible_def greedyOwnerIndex`, not a custom axiom or user-facing
`opaque` declaration.

### 5.4 V6 vacuity and triviality

| Measurement | Pre-removal review | Active V6 |
|---|---:|---:|
| Physical files scanned by Tier A | 224 | **222** |
| Tier-A parsed declarations | 7,421 | **7,411** |
| Tier-A red-flag rows | 13 | **13** |
| Tier-A reviewed false positives | 13 | **13** |
| Complete Tier-B review assignments | 786 | **779** |
| Tier-B status | 784 OK / 2 SUSPECT | **779 OK / 0 SUSPECT / 0 VACUOUS** |
| Mandatory union rows | 709 | **702** |
| Supplemental direct-census rows | 98 | **91** |
| Resolved declaration references | 749 | **744** |
| Unique project theorem endpoints | 524 | **519** |
| Explicit exclusions | 126 | **124** |

The active Tier-C protocol covers **103 rows = 50 retained fixed controls +
50 manifest-seeded controls + 3 Tier-A escalations**. Its evidence is 91
compiled-witness rows, referencing 93 declarations, plus 12 exact clean V4
citations. No like-for-like pre-removal total for this refreshed seeded
protocol is asserted. The former positive-Ricci, arbitrary-set upper-Chevet,
and conditional Borell families are absent; finite zero-containing Chevet
and arbitrary-set reverse Chevet remain.

### 5.5 V7 definition sanity

| Measurement | Pre-removal V7 | Active V7 |
|---|---:|---:|
| Environment modules | 225 | **223** |
| Project constants | 15,052 | **15,022** |
| Dependency edges | 1,450,620 | **1,448,224** |
| V6 theorem endpoints used | 524 | **519** |
| Load-bearing union | 273 | **270** |
| Exact-gated citations | 231 | **228** |
| Witness-backed rows | 42 | **42** |
| Named witness theorems | 37 | **37** |
| Unverified / unreviewed rows | 0 / 0 | **0 / 0** |
| Zero-reverse rows before exclusions | 4,296 | **4,280** |
| Documented exclusions | 2,291 | **2,283** |
| Dead-code candidates | 2,005 | **1,997** |

All 270 active load-bearing rows retain positive evidence. A dead-code
candidate is an informational reachability result, not a deletion
recommendation.

### 5.6 V8 package lint

| Measurement | Pre-removal V8 | Active V8 |
|---|---:|---:|
| Physical source files covered | 224 | **222** |
| Declarations examined | 8,677 | **8,662** |
| Automatically generated declarations | 6,375 | **6,360** |
| Unique declaration-level lint rows | 166 | **68** |
| Modules with lint rows | 46 | **30** |
| `structureInType` rows | 1 | **0** |
| `docBlame` rows | 97 | **0** |

The active 68 rows split exactly into **48 unused-argument, 13
simplifier-normal-form, 4 declaration-form, 2 naming, and 1
simplifier-commutativity** advisory. The deleted
`GaussianChevetUpperPrinciple` supplied the former proposition-only-structure
row. Round 10 repaired all 97 missing declaration docstrings in 25 files;
the certified delta added documentation only and changed no declaration,
signature, or proof body. V8 is a quality gate, not evidence that any theorem
is false or unproved.

### 5.7 V10 conditional interfaces

The measured pre-removal all-theorem proposition-binder population was
15,406; the active population is **15,381**. The active named census has
**352 primary candidates = 319 predicates + 33 interfaces**, classified as
**86 PROVED, 250 CONSUMED-ONLY, and 16 DEAD**. It also classifies **4,734
inline review rows**, including a 2,911-row exact digest-bound structural
population.

No separate like-for-like pre-removal primary-status or 4,734-row inline
summary was retained, so no baseline is inferred for those two populations.
The active checks establish exact absence of all **12 removed declarations**
and both removed source files, retain **2/2** finite-Chevet `hzero : 0 ∈ T`
signatures, and replay **15** current Appendix/V6 axiom endpoints. The only
finding is ten INFO-level, source-disclosed infrastructure items with
unpublished consumers; no Tier-B published result depends on them.

## 6. Coverage boundary

Every book item that remains in the 611-row publication map is covered. The only excluded scopes are equation (5.8), the arbitrary-set forms of Exercise 8.39(a) and Remark 8.6.3, and the Borell half of Example 3.4.6; their source-facing conditional or assumption-strengthened interfaces were removed on 2026-07-20. Finite-set Chevet results and Exercise 8.39(b) remain covered.

No excluded scope is represented as a completed theorem. The frozen 838-row
census remains byte-authentic historical provenance; the 835-row active
projection is a separate overlay and does not rewrite that input.

## 7. Appendix outcomes

| Source obligation | Final active outcome |
|---|---|
| Arbitrary-set Exercise 8.39(a) and Remark 8.6.3 | Removed from source-facing coverage. Finite-set upper results with visible `0 ∈ T` and the unconditional reverse result for Exercise 8.39(b) remain. |
| Equation (5.8) | Removed from source-facing coverage. Reusable Bakry--Émery and diffusion infrastructure remains but is not counted as equation-(5.8) coverage. |
| Borell half of Example 3.4.6 | Removed from source-facing coverage. The retained module contains only unconditional domain support. |
| Remark 7.2.1 Brownian reflection | Source-faithfully proved at the finite-subfamily `extendedExpectedSupremum : EReal` interface. |

The active Appendix registry is therefore **14/14 source-faithful PROVED,
0 assumption-strengthened, and 0 skipped**. The aggregator's fifteenth direct
import is retained Borell domain infrastructure, not a fifteenth registered
target. There is no active `APPENDIX-UNRESOLVED-NNN` theorem or deferred
census row.

## 8. Active V1--V10 verdicts

Finding counts are ordered Critical / Major / Minor / Info.

| Gate | Verdict | Findings | Controlling report |
|---|---|---:|---|
| V1 -- build integrity | PASS-WITH-NOTES | 0/0/0/1 | [V1](01_build_integrity.md) |
| V2 -- import-graph completeness | PASS | 0/0/0/0 | [V2](02_import_graph.md) |
| V3 -- placeholder census | PASS-WITH-NOTES | 0/0/0/1 | [V3](03_sorry_audit.md) |
| V4 -- exhaustive axiom audit | PASS-WITH-NOTES | 0/0/0/1 | [V4](04_axiom_audit.md) |
| V5 -- escape-hatch audit | PASS-WITH-NOTES | 0/0/0/4 | [V5](05_escape_hatches.md) |
| V6 -- vacuity and triviality | PASS | 0/0/0/0 | [V6](06_vacuity_triviality.md) |
| V7 -- definition sanity | PASS-WITH-NOTES | 0/0/0/3 | [V7](07_definition_sanity.md) |
| V8 -- linter and quality | PASS-WITH-NOTES | 0/0/0/3 | [V8](08_linter_report.md) |
| V9 -- published claims | PASS | 0/0/0/0 | [V9](09_readme_claims.md) |
| V10 -- conditional interfaces | PASS-WITH-NOTES | 0/0/0/1 | [V10](10_conditional_interfaces.md) |
| **Total** | -- | **0/0/0/14** | [Verification index](README.md) |

The V9 currentness replay records 66 documentation-claim rows: 60 `MATCH`,
zero `STALE`, zero `OVERSTATED`, and six static-scope `UNVERIFIABLE` rows.
Those six are declared limits of the static checker rather than actionable
claim defects. The separate endpoint check passes all 611 correspondence
rows and 540 names.

The Verification README consistency checker currently reports ten reports,
ten index rows, 14 report findings, 14 summary findings, zero problems, and
`PASS`.

## 9. Correct-to-re-verify history

1. **Round 1 -- foundational corrections.** Applied F-01/F-02/F-04--F-11
   in dependency order; revalidated F-12/F-13 and rejected F-14.
2. **Round 2 -- first downstream rebuild.** Rebuilt the first affected
   modules after the foundational definition repairs and closed the exposed
   proof and elaboration obligations.
3. **Round 3 -- later dependency cones.** Continued the definitional-ripple
   review through later consumers, including the Chapter 7 and Chapter 8
   cones, and checked statement meaning even where compilation succeeded.
4. **Round 4 -- downstream fixed point.** Closed the remaining consumer
   obligations and replayed the affected whole-tree and Appendix build
   surfaces to green.
5. **Round 5 -- PDF faithfulness replay.** Rechecked all corrected and added
   statements and the five former partial rows against the original rendered
   PDF; no new editable faithfulness defect survived.
6. **Round 6 -- combined Pass 05/06 replay.** Validated all historical
   non-INFO soundness findings; repaired the Bernoulli gradient helper,
   Berry--Esseen import, stale keys, and publication records; and applied the
   then-selected Appendix dispositions.
7. **Round 7 -- pre-closure fixed point.** Regenerated graph, V6, V7,
   placeholder, documentation, publication, build, and axiom evidence.
8. **Round 8 -- 2026-07-19 historical closure.** Rechecked the four Appendix
   questions and produced the then-current build and V4 evidence.
9. **Round 9 -- 2026-07-20 post-restructuring closure and scope removal.** Replayed all Pass 05
   findings, closed the former V7 evidence gaps, checked the full 225-module
   pre-removal environment, refreshed V1--V10, and synchronized publication
   and documentation evidence. It then removed the three non-source-faithful
   scopes, generated the 835-row active census, and re-certified the resulting
   222-file/223-module source through V1--V10.
10. **Round 10 -- 2026-07-21 documentation closure.** A fresh package-lint
   replay showed that the active source still contained the 97 `docBlame`
   rows that an earlier narrative had prematurely described as fixed. Added
   exactly 97 one-line declaration docstrings across 25 Lean files, certified
   the change as documentation-only against the preserved
   `83678e994eecf416759cb099d5e69f9d03c15921960d4f3b69d055a7a9e8fe27`
   source baseline, and re-ran the complete V1--V10 currentness and acceptance
   sequence at digest
   `bca641bd4c523754aa472b97cb1ed5638a6eb7361f99158a3f231a03a7446460`.
   The clean round has zero Critical, Major, or Minor findings; its 14
   remaining findings are INFO-only boundaries and advisories.
11. **Round 11 -- 2026-07-21 Exercise and records reorganization phase.** Moved all
   67 Exercise modules into `Exercise/Chapter1`--`Exercise/Chapter9`, updated
   their physical module imports without renaming the public
   `HDP.ChapterN.Exercise` API, and reduced the source-root Markdown surface to
   the README, Appendix summary, and human verification log. Current reports
   moved under `Verification/` and five predecessor records under
   `Verification/archive/`. The exact move certificate binds the Round-10
   digest to
   `78da8753a3367be0ae4c72df049a99f33723a7b22a1d08384714cc59d08853d4`;
   full path-sensitive V1--V10 and final consistency replay is intentionally
   deferred until the owner's additional changes are applied. The interrupted
   V4 shard is not installed evidence.

There are **10 completed correction/reverification rounds**. Round 11 is an
open layout/change phase whose combined replay is intentionally deferred.
Rounds 1--5 are retrospective source-record subdivisions under the
2026-07-18 report date; no independent timestamped execution log is claimed
for each subdivision.

The current numbered reports and their source-bound artifacts are the
controlling evidence, not an earlier copied count in this narrative.

## 10. Rounds 10--11 changed-file inventory

The Round-10 Lean delta is exactly 25 files, all documentation-only:

- Appendix infrastructure: `BakryEmery.lean`,
  `BerryEsseenAssembly.lean`, `BerryEsseenCertificate.lean`,
  `BerryEsseenGaussianInversion.lean`, `BerryEsseenInversion.lean`,
  `BerryEsseenVaaler.lean`, `PoincareWeak.lean`,
  `SpecialOrthogonalQuotientAnalytic.lean`,
  `SpecialOrthogonalQuotientGeometry.lean`,
  `SpecialOrthogonalTwoLogSobolev.lean`, `SphericalPolarization.lean`,
  `SphericalSymmetrization.lean`, `SymmetricGroupCode.lean`, and
  `TalagrandConvexFunction.lean`;
- consolidated core and exercise leaves:
  `Exercise/Chapter3/Sec06.lean`,
  `Chapter3_RandomVectorsInHighDimensions.lean`,
  `Chapter4_RandomMatrices.lean`,
  `Chapter5_ConcentrationWithoutIndependence.lean`,
  `Exercise/Chapter8/Sec02.lean`, `Sec04.lean`, and `Sec05.lean`,
  `Chapter8_Chaining.lean`, `Exercise/Chapter9/Sec01.lean`, and
  `Chapter9_DeviationsOfRandomMatricesOnSets.lean`; and
- Prelude: `Prelude/MetricEntropy.lean`.

The source-delta certificate lists every added docstring with its current
line and both file hashes. No MatrixConcentration Lean file changed. The main
source README received one mathematical-typesetting repair to its displayed
Chebyshev bound; that record edit is outside the authenticated Lean-source
manifest. Round 10 added **97 declaration docstrings**, changed **0 Lean book
citations**, and corrected **1 README mathematical display**.

The exact hand-edited verification scripts are:

- `build_v6_tier_b_ch0_4.py`, `build_v6_tier_b_ch5_7.py`,
  `build_v6_tier_b_ch8_9.py`, `build_v6_tier_b_supplement_ch0_4.py`,
  `build_v6_tier_b_supplement_ch5_7.py`, and
  `build_v6_tier_b_supplement_ch8_9.py`;
- `build_v6_tier_c_seeded_sample.py`, `check_v6_final.py`,
  `recert_v6_tier_c.py`, and `run_v6_tier_c_ch5_7.py`;
- `install_recert_v4_merge.py`, `row_inventory.py`, `run_all.sh`,
  `v1_build_integrity.py`, `v3_ledger_reconciliation.py`, and the new
  `verify_round10_docstring_delta.py`.

The exact hand-edited narrative/record files are `README.md`,
`Verification/REVIEW_NOTES.md`, `Verification/CORRECTION_LEDGER.md`,
`Verification/FINAL_CORRECTION_REPORT.md`,
`Verification/archive/FAITHFUL_PROOFREAD_REPORT.md`, Verification reports
`01`, `03`, `04`, `05`, `06`, `07`, `08`, `09`, and `10`,
`Verification/README.md`, and `HUMAN_VERIFICATION_LOG.md`. V2 required fresh
evidence replay but no hand
edit to its controlling report.

The row-inventory generator mechanically refreshed its authenticated JSON/TSV
outputs, and the V3--V10 commands refreshed their named `logs/`, `review/`,
and inventory evidence. The controlling acceptance transcripts enumerate and
hash that exact final generated record set; generated logs and run-state
directories are evidence outputs rather than hand-edited source.

Round 11 then moved, without deleting or merging, the 67 Exercise Lean files
into `Exercise/Chapter1`--`Exercise/Chapter9`. Fifty-two moved files are
byte-identical; the other 15 contain only the import-token changes forced by
their new physical module names. The root aggregator has nine corresponding
import rewrites, and four other Lean files have path/module text changed only
inside comments. The all-source certificate enumerates all 67 old/new path
pairs and proves zero other source difference.

At the record layer, `APPENDIX_SUMMARY.md` and
`HUMAN_VERIFICATION_LOG.md` now sit beside the source README. The current
review notes, correction ledger, final report, and numbered checks sit below
`Verification/`; the five immutable predecessor documents sit below
`Verification/archive/`. Path-sensitive V3/V4/V6--V10 generators and gates
were re-anchored to the new physical modules, while their final generated
artifacts await the additional requested changes and combined replay. Round 11 also adds
`verify_exercise_reorganization.py` and
`verify_reorganization_layout.py`; the latter is part of the final
orchestrator consistency stage and rejects a stale current report or review
packet even when the Lean build itself succeeds.

## 11. Trust boundary, records, and unchanged inputs

The toolchain remains Lean `v4.31.0` at commit
`68218e876d2a38b1985b8590fff244a83c321783`, Lake
`5.0.0-src+68218e8`, and Mathlib revision
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. Mechanical guarantees remain
conditional on the Lean kernel and pinned dependency packages.

The verbatim pre-correction review is
[`REVIEW_NOTES.pre-final-correction.md`](archive/REVIEW_NOTES.pre-final-correction.md),
SHA-256
`53ac710d7882078e460ba9df8f7d94e9ca37110924ce17d86ecd991480ab1dc1`.
[`FAITHFUL_PROOFREAD_REPORT.md`](archive/FAITHFUL_PROOFREAD_REPORT.md) preserves the
historical Pass 05 body beneath an active closure notice.
[`REVIEW_NOTES.md`](REVIEW_NOTES.md) is the active coverage reconciliation,
[`CORRECTION_LEDGER.md`](CORRECTION_LEDGER.md) is the row-level correction
record, the local project record `../APPENDIX_SUMMARY.md` is the active target
registry plus historical dossier, and
[`Verification/README.md`](README.md) indexes the mechanical
evidence.

No MatrixConcentration source, `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`, or vendored dependency was edited. The exact correction
and same-name-change inventories remain under `Verification/inventory/`; the
scope-removal list in section 3 is the exact later deletion surface.

## 12. Final synchronization protocol

Acceptance requires an exit-0 manifest-first orchestration followed by an
exit-0 re-entrant replay with the same source, scratch, inventory, toolchain,
reports, and evidence hashes. The [first accepted transcript](logs/run_all_first_acceptance.log)
and [immediate no-drift replay](logs/run_all_no_drift_replay.log)
are preserved separately; the replay also remains the
[controlling transcript](logs/run_all.log). An earlier failed or
transient-state run is not final evidence. This report is intentionally stable
across those two runs, so recording the replay does not itself invalidate the
document hashes that the orchestration checks.
