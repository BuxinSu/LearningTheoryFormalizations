> **Round-10 post-removal closure notice (2026-07-21).** The body below is the
> historical Pass 05 audit and is preserved as written. Its counts, defect
> descriptions, and “final” verdict describe the pre-correction input, not the
> active tree. Pass 07 independently classified F-01--F-14 as
> **9 CONFIRMED / 4 REVISED / 1 REJECTED** and corrected every actionable core
> finding; the historical Pass 06 population was independently classified as
> **10 CONFIRMED / 14 REVISED / 1 REJECTED**.
> The active V1--V10 population is **0 Critical / 0 Major / 0 Minor / 14
> Info**. Round 10 repaired the 97 missing declaration docstrings that were
> still present after Round 9; the independent delta certificate records 97
> one-line docstrings in 25 Lean files, one replaced blank line, and zero
> nonblank non-documentation source change. Fresh package lint has zero
> `docBlame` and 68 INFO-only API/name/automation advisories; see
> `Verification/logs/round10_docstring_delta.log`.
>
> Per-finding closure rounds are explicit:
>
> | Pass 05 ID | Closure round |
> |---|---|
> | F-01, F-02, F-04--F-11 | Corrected in Round 1 and replayed against the PDF in Round 5. |
> | F-03 | Initially validated in Round 1; finally resolved by the 2026-07-20 post-Round-9 scope removal. |
> | F-12, F-13 | Revalidated in Round 1 and replayed in Round 5; no separate code edit was required. |
> | F-14 | Rejected as a stronger, faithful positive-domain extension in Round 1; rejection reconfirmed in Round 5. |
>
> The active source has **222 physical modules (212
> HighDimensionalProbability + 10 MatrixConcentration)** and **223 import-graph
> nodes including the root aggregator**. Every physical module lies on a
> checked import/build surface, with zero orphan, unresolved-import, or cyclic
> module. The former `Pre_MatrixConcentration` subtree remains absent.
>
> The active mathematical projection is **835 = 769 core-formalized + 66
> Appendix-proved + 0 deferred/source-limited**, with zero core-partial and
> zero missing in-scope conclusions. The publication map remains **611/611
> verified mappings** over **540 unique endpoints**. Exactly **228 executable
> `sorry` proofs** remain, all intentional, marked Exercise leaves; Appendix
> and load-bearing support code contain none. The active Appendix registry is
> **14/14 source-faithful proved**. Its 15 direct imports include the retained
> `BorellConvexBody.lean` domain-support module, which is infrastructure rather
> than a registered target.
>
> On 2026-07-20 the source-facing conditional or assumption-strengthened
> interfaces for equation (5.8), arbitrary-set Exercise 8.39(a) and Remark
> 8.6.3, and the Borell half of Example 3.4.6 were removed instead of being
> presented as coverage. The direct finite-set Gaussian-Chevet theorems remain
> with explicit `0 ∈ T`, and Exercise 8.39(b) remains covered.
> `RiemannianDiffusionLaw`, the reusable Bakry--Émery infrastructure, and the
> independently discharged special-orthogonal and Grassmannian concentration
> routes remain.
>
> The active documentation contract is **6,073/6,073 non-Appendix target
> declarations in 101 files**, with zero label or citation-shape defect.
> Section A of the sibling human-proofread register now has **496 applicable
> rows**; the two deleted endpoint rows and semantic rows S8--S10 are marked
> N.A. Final mechanical counts, findings, and evidence boundaries are
> controlled by `Verification/README.md`, `REVIEW_NOTES.md`, and
> `FINAL_CORRECTION_REPORT.md`, not by the historical body below.
>
> The verbatim pre-correction and pre-removal records remain available as
> provenance. In particular, the PDF's Exercise 8.39(a) Sudakov--Fernique hint
> was not refuted; only the non-source-faithful conditional interface was
> removed. The active scope and retained finite theorem are documented in
> `Appendix/APPENDIX_SUMMARY.md`.
>
> The verbatim pre-correction review input remains
> `REVIEW_NOTES.pre-final-correction.md` with SHA-256
> `53ac710d7882078e460ba9df8f7d94e9ca37110924ce17d86ecd991480ab1dc1`.

# Final faithfulness, comprehensiveness, and correctness proofread

Date: 2026-07-17

## Executive verdict

The final PDF-grounded census contains **838 valid conclusions**:

- **763 core-formalized**;
- **5 core-partial**;
- **65 appendix-proved**;
- **5 appendix-unresolved/deferred**;
- **0 missing** and **0 unsure**.

The frozen 873-row input also contained **35 rows that are not separate
in-scope conclusions** after PDF revalidation. The **191 non-load-bearing
practice-exercise numbers** remain intentionally out of scope.

The root development and isolated appendix both build. All 534 unique Lean
endpoints used by the 611-row publication map are free of `sorryAx` and
project-specific axioms. The appendix has **13 source-faithful proved targets
and 2 honestly unresolved targets**:
`APPENDIX-UNRESOLVED-001` (sharp arbitrary-set Gaussian Chevet) and
`APPENDIX-UNRESOLVED-002` (the positive-Ricci geometry-to-analysis bridge).

Five compiled core rows are not faithful complete captures and are therefore
`PARTIAL`: Exercises 3.18, 3.19, and 3.20; Remark 7.2.1; and equation (8.37).
No core Lean declaration, statement, proof, name, location, or docstring was
changed in this pass.

## 1. Scope, source, and method

The authoritative source was the original second-edition PDF:

`High_Dimensional_Probability/Original_High_Dimensional_Probability.pdf`

The generated LaTeX was not used for content or numbering. Existing
inventories and audit records were used only as search aids and were checked
against the PDF. The final review covered the Appetizer, Chapters 1–9, shared
Prelude definitions, load-bearing exercise endpoints, all exercise leaves,
and the isolated appendix.

The decisive PDF comparisons were visually rendered from the original PDF,
including physical pages 19, 27, 35, 46, 53, 73, 75, 81, 100–101, 151–158,
174, 207, 215, 222, 251, and 257–260. These cover the foundation definitions,
Exercises 3.18–3.20, all materially corrected appendix statements, the two
core junk-value findings, the two publication-map defects, and the majorizing
measure/Chevet targets.

The audit deliberately separated three questions:

1. Does Lean prove the stated proposition?
2. Does the proposition and every source-facing definition mean what the PDF
   says?
3. Is every in-scope PDF conclusion present?

This separation is essential: axiom-clean proofs can still be unfaithful
because of a rigged definition, a junk value, a wrong object, or an
uninstantiated interface.

## 2. Reconciled starting state

### 2.1 Census records

The records previously mixed three denominators:

| Stage | Formalized | Partial / historical gap | Missing | Appendix-owned | Rejected | Total input |
|---|---:|---:|---:|---:|---:|---:|
| Frozen audit snapshot | 717 | 55 | 34 | 67 | 0 | 873 |
| PDF correction pass | 768 | 0 | 0 | 70 | 35 | 873 |
| Final semantic audit | 763 | 5 | 0 | 70 = 65 proved + 5 unresolved | 35 | 873 |

The frozen gap inventory had 89 entries: 45 `PARTIAL`, 34 `MISSING`, and 10
`UNSURE` (the public historical summary grouped all 55 non-missing gap labels
together). PDF revalidation assigned those 89 entries as follows:

- 51 are faithfully formalized;
- 35 are not separate in-scope conclusions;
- 3 belong at the appendix/deferred boundary.

The 611-row README table is a curated publication map, not the 873-row frozen
audit and not the 838-conclusion exhaustive census. Its final status is **609
verified / 2 partial**.

### 2.2 Appendix record discrepancy

The stale appendix records claimed “4 proved / 11 external.” The live code did
not support that description. Target-level inspection found:

- thirteen source-faithful, placeholder-free target proofs;
- one literal target placeholder, Gaussian Chevet;
- one axiom-clean analytic implication, positive Ricci, that does not
  instantiate the book's geometric hypotheses.

Thus the truthful semantic status was and remains **13 proved / 2
unresolved**, not 4/11 and not 14/1. A clean axiom printout for positive Ricci
does not close its quantifier/hypothesis gap.

### 2.3 Build and source-token ground truth

The first live root build in this pass and the final root build both completed
**8,670 / 8,670 jobs**. The isolated appendix build is separately required
because the package root intentionally does not import it; its final result is
recorded in §7.

The first live source-token sweep—and the final sweep—found:

| Lean identifier token | Core / Prelude / root | Exercise leaves | Appendix | Total |
|---|---:|---:|---:|---:|
| `sorry` | 0 | 228 | 1 | 229 |
| `sorryAx` | 0 | 0 | 0 | 0 |
| `admit` | 0 | 0 | 0 | 0 |
| `native_decide` | 0 | 0 | 0 | 0 |
| ordinary `decide` | 21 | 4 | 5 | 30 |
| declaration token `axiom` | 0 | 0 | 0 | 0 |
| `unsafe` | 0 | 0 | 0 | 0 |

- zero `sorry`, `admit`, theorem-level `axiom`, or `unsafe` in the 25
  core/Prelude files;
- 228 `sorry` occurrences in 46 `ChapterN/Exercise/` leaf files, all carrying
  an `EXERCISE-SORRY` marker;
- one appendix `sorry`, exactly the tagged
  `APPENDIX-UNRESOLVED-001` Gaussian-Chevet target;
- no appendix `admit`, theorem-level `axiom`, `native_decide`, or `unsafe`;
- no source occurrence of `sorryAx`; it appears only in the kernel axiom
  report for the one unresolved Chevet target.

This also resolves the task scaffold's anticipated “three appendix literal
sorries”: in the live starting tree, Berry–Esseen and special-orthogonal
concentration already had complete proof bodies written before this final
pass. Only Gaussian Chevet still contained `sorry`.

Ordinary `decide`/`by decide` uses are computational proof terms and were
audited separately from the forbidden `native_decide`: 11 are concrete finite
or arithmetic computations, and the other 19 turn decidable propositions
into Boolean filters, sign bits, membership tests, or finite encodings. None
introduces an axiom or a hidden placeholder.

## 3. Faithfulness catalogue

The catalogue below is complete for the final audit. “Critical” means a
purportedly proved/source-facing item does not express the book's object or
can return a mathematically wrong value. “Major” means a materially incomplete
specialization, a defective foundation API with safe restricted consumers, or
a publication map that overstates its endpoint. “Minor” is a documented
off-domain convention.

### 3.1 Critical findings

#### CRITICAL F-01 — Exercise 3.19 is definitionally rigged

- **Lean:** `HDP.Chapter3.gaussianSymmetrizedLaw`,
  `HDP.Chapter3.exercise_3_19a`, `HDP.Chapter3.exercise_3_19b`
- **Location:** `Chapter3_RandomVectorsInHighDimensions.lean:9553`,
  `:9565`, `:9577`
- **Book:** **Book Exercise 3.19**, physical pages 100–101 / printed
  pages 92–93
- **Defect class:** proof-by-definition; wrong object; uninstantiated
  commuting-square interface

The PDF defines the Gaussian Orthogonal Ensemble through independent matrix
entries (diagonal law `N(0,2)`, off-diagonal law `N(0,1)`), asks for the
representation `(G+Gᵀ)/√2`, and then orthogonal-conjugation invariance. Lean
instead defines `gaussianSymmetrizedLaw E F S` to be
`Measure.map S (stdGaussian E)`, so part (a) is `rfl`. There is no symmetric
matrix space, GOE entry law, independence, transpose, or variance
calculation. Moreover `F` has only an arbitrary measurable space, not a
`BorelSpace`; continuity of `S` therefore does not imply the measurability
needed by `Measure.map`, whose off-domain value is the zero measure. Part (b)
assumes the hard commuting identity. The result is `PARTIAL`.

#### CRITICAL F-02 — Exercise 3.20 assumes the product law it should derive

- **Lean:** `HDP.Chapter3.exercise_3_20`
- **Location:** `Chapter3_RandomVectorsInHighDimensions.lean:9612`
- **Book:** **Book Exercise 3.20**, physical page 101 / printed page 93
- **Defect class:** wrong object; tautological product-law substitution

The PDF starts with a Ginibre matrix `G` and orthogonal unit vectors `u,v`,
then asks to prove `Gu` and `Gv` are independent standard Gaussian vectors.
Lean starts on `(stdGaussian F).prod (stdGaussian F)` and uses `Prod.fst` and
`Prod.snd`. It contains no `G`, `u`, `v`, matrix multiplication,
orthogonality, or derivation of the joint product law. The result is
`PARTIAL`.

#### CRITICAL F-03 — Positive Ricci remains an uninstantiated certificate

- **Lean:** `HDP.Chapter5.positive_ricci_concentration`;
  premise `HDP.Chapter5.IsPositiveRicciRiemannianLaw`
- **Location:** `Appendix/PositiveRicciConcentration.lean:54`;
  premise at `:18`; analytic certificate in
  `Appendix/Infra/BakryEmery.lean:317`
- **Book:** **Book equation (5.8)**, physical page 156 / printed page 148
- **Defect class:** conditional/uninstantiated interface; stronger assumed
  analytic data; missing geometry-to-analysis bridge

The PDF quantifies over compact connected Riemannian manifolds with geodesic
distance, normalized Riemannian volume, and actual Ricci tensor satisfying
`Ric(v,v) ≥ κ‖v‖²`. Lean proves a genuine Bakry–Émery implication from a
diffusion/Bochner certificate, but nowhere constructs that certificate from
an actual Riemannian manifold and its Ricci lower bound. The only occurrences
of `IsPositiveRicciRiemannianLaw` are its declaration and consumers. This is
therefore `APPENDIX-UNRESOLVED-002`, even though its axiom output is clean.

#### CRITICAL F-04 — arbitrary-index expected supremum loses `+∞`

- **Lean:** `HDP.Chapter7.extendedExpectedSupremum`; finite component
  `HDP.Chapter7.expectedFiniteSupremum`
- **Location:** `Chapter7_RandomProcesses.lean:9953`; finite component
  at `:2778`
- **Book:** **Book Remark 7.2.1**, physical page 207 / printed page 199
- **Defect class:** wrong codomain at the finite stage; Bochner-integral
  junk value

The PDF defines the arbitrary-index expectation as the supremum of
finite-subset expected maxima, which may be `+∞`. Lean's outer value is
`EReal`, but each finite expectation is first computed by a real Bochner
integral. Mathlib defines a nonintegrable real integral to be zero, so casting
afterward cannot recover infinity. A nonnegative one-coordinate process with
infinite expectation is therefore assigned zero. The row is `PARTIAL`.

#### CRITICAL F-05 — population squared risk assigns infinite loss zero

- **Lean:** `HDP.Chapter8.populationRisk`; downstream
  `HDP.Chapter8.IsPopulationRiskMinimizer`
- **Location:** `Chapter8_Chaining.lean:17294`; minimizer API at `:17334`
- **Book:** **Book equation (8.37)**, physical page 251 / printed page 243
- **Defect class:** real-integral junk value; spurious minimizer

The PDF's risk `E(f(X)-T(X))²` may be infinite without an integrability
assumption. Lean returns a real Bochner integral with no measurability or
integrability premise, hence zero for a nonintegrable squared loss. Such a
predictor can become a false zero-risk minimizer. The Boolean VC-risk API is
separate and bounded, so it is not affected. Equation (8.37) is `PARTIAL`.

### 3.2 Major findings

#### MAJOR F-06 — Exercise 3.18 omits the Ginibre specialization

- **Lean:** `HDP.Chapter3.exercise_3_18`
- **Location:** `Chapter3_RandomVectorsInHighDimensions.lean:9540`
- **Book:** **Book Exercise 3.18**, physical page 100 / printed page 92
- **Defect class:** incomplete specialization; over-claiming source map

Lean proves standard-Gaussian invariance under two already supplied Hilbert
isometries. It never constructs the Ginibre matrix law or proves that left and
right multiplication by an orthogonal matrix are those isometries. No
project declaration instantiates the interface. The row is `PARTIAL`.

#### MAJOR F-07 — scalar `ψ₂`/`ψ₁` predicates omit random-variable conditions

- **Lean:** `HDP.psi2MGF`, `HDP.SubGaussian`, `HDP.psi2Norm`,
  `HDP.psi1MGF`, `HDP.SubExponential`, `HDP.psi1Norm`
- **Location:** `Chapter2_ConcentrationOfIndependentSums.lean:2755`,
  `:2763`, `:2770`, `:7152`, `:7160`, `:7167`
- **Book:** **Book Definitions 2.6.4 and 2.8.4**
- **Defect class:** omitted measurability and probability-space conditions

The raw predicates accept arbitrary functions under arbitrary measures. They
therefore include non-random functions and become trivial under the zero
measure. Their infimum sets correctly require `K>0`, but the unrestricted MGF
helpers also expose Lean's `/0=0` boundary. The coverage rows remain valid
only through the measurable probability-space theorem families such as
`psi2MGF_psi2Norm_le_two` and `psi1MGF_psi1Norm_le_two`; README now states
that qualification explicitly. The separate equation (2.15) row now points
to the measurable probability-space tail theorem `subgaussian_iii_to_i`, not
to the raw MGF-based predicate.

#### MAJOR F-08 — isotropy/second moments are totalized off domain

- **Lean:** `HDP.secondMomentMatrix`, `HDP.IsIsotropic`,
  `HDP.isIsotropic_iff`
- **Location:** `Prelude/RandomVector.lean:26`, `:89`, `:95`
- **Book:** **Book Definition 3.2.5**
- **Defect class:** omitted measurability, second-moment, and probability
  hypotheses

The raw definitions can hold for a nonmeasurable sign-valued function and use
the zero value of a nonintegrable Bochner integral. Safe Chapter 3 identities,
including `HDP.Chapter3.secondMoment_inner_sq`, restore coordinate-product
integrability; source-facing use must still carry measurability of `X`
separately. The census row remains covered only with those domain caveats.

#### MAJOR F-09 — vector `ψ₂` totalizes a potentially unbounded supremum

- **Lean:** `HDP.SubGaussianVector`, `HDP.psi2NormVector`,
  `HDP.psi2Norm_marginal_le_vector`
- **Location:** `Prelude/RandomVector.lean:178`, `:189`, `:197`
- **Book:** **Book Definition 3.4.1**
- **Defect class:** inherited measurability defect; real `sSup` off its
  bounded domain

The vector predicate inherits F-07. Its real-valued `sSup` definition has no
built-in nonemptiness or boundedness, while its comparison theorem must assume
`BddAbove`. README now limits the source-facing claim to measurable
probability spaces and the bounded-supremum regime.

#### MAJOR F-10 — Gaussian-vector law accepts non-PSD “covariances”

- **Lean:** `HDP.HasGaussianVectorLaw`
- **Location:** `Prelude/RandomVector.lean:208`
- **Book:** **Book Definition 3.3.4**
- **Defect class:** wrong covariance domain

The raw predicate has no positive-semidefinite premise. Mathlib totalizes a
multivariate Gaussian with a non-PSD covariance as a Dirac law, so the
predicate can falsely label an arbitrary non-PSD matrix as a covariance. The
published row is nevertheless covered by
`HDP.Chapter3.hasGaussianVectorLaw_iff_affineRepresentation`, which explicitly
assumes PSD and constructs `S=AAᵀ`.

#### MAJOR F-11 — real expectation/norm helpers share an off-domain zero

- **Lean:** `HDP.Chapter1.lpNormRV`, `mgf_def'`, `l2InnerRV`,
  `covariance_def'`, `covMatrix`; `HDP.secondMomentMatrix`
- **Location:** `Chapter1_AnalysisAndProbabilityRefresher.lean:891`,
  `:923`, `:995`, `:1034`, `:1053`; `Prelude/RandomVector.lean:26`
- **Book:** **Book equations (1.10)–(1.13)** and the MGF discussion
- **Defect class:** Bochner-integral junk-value family

The book's real-valued formulas live on finite-moment domains, while an MGF
may be infinite. The unrestricted real helpers return zero for nonintegrable
inputs. Safe endpoints use `eLpNorm`, `MemLp`, or explicit integrability; the
README now maps equation (1.10) to `eLpNorm` plus
`lpNormRV_eq_toReal_eLpNorm`, maps equations (1.11) and (1.13) through
`MeasureTheory.L2.inner_def`, `ProbabilityTheory.covariance_eq_sub`, and the
restricted Chapter 3 covariance identities, and identifies the MGF helper's
finite domain.

#### MAJOR F-12 — equation (7.14) was mapped only to a finite endpoint

- **Record:** former README map to
  `HDP.Chapter7.expectedFiniteSupremum`
- **Location:** `README.md:612` after correction
- **Book:** **Book equation (7.14)**, physical page 215 / printed page 207
- **Defect class:** publication endpoint/scope mismatch

The PDF quantifies over an arbitrary index set, whereas the old endpoint was
finite. A full-scope declaration already exists. The README now maps the row
to `extendedExpectedSupremum` and lists the finite theorem only as its engine.
This finding changes no census status.

#### MAJOR F-13 — Theorem 7.6.1 was mapped only to a finite set

- **Record:** former README map to
  `HDP.Chapter7.randomProjection_expectedDiameter`
- **Location:** `README.md:597` after correction
- **Book:** **Book Theorem 7.6.1**, physical page 222 / printed page 214
- **Defect class:** publication endpoint/scope mismatch

The PDF treats every nonempty bounded set. The old mapped declaration treated
a `Finset`; the faithful arbitrary-set endpoint already existed as
`HDP.Chapter9.haarProjection_expectedDiameter_set`. README now points to that
endpoint and retains the finite theorem as its engine. This finding changes no
census status.

### 3.3 Minor finding

#### MINOR F-14 — conditional probability extends the zero denominator

- **Lean:** `HDP.Chapter1.cond_real_def`
- **Location:** `Chapter1_AnalysisAndProbabilityRefresher.lean:1233`
- **Book:** **Book Section 1.5**
- **Defect class:** documented total extension

The book's ratio is meaningful for `P(F)>0`. Lean consistently makes both
sides zero when `P(F)=0`, and its docstring says so. This is a harmless,
documented extension, not a false positive-domain theorem and not a census
demotion.

### 3.4 Severity summary

| Severity | Count | Effect |
|---|---:|---|
| Critical | 5 | four core rows demoted plus one appendix target unresolved |
| Major | 8 | one core row demoted; five foundation APIs qualified; two README maps corrected |
| Minor | 1 | documented off-domain extension |
| **Total** | **14** | **five core partial rows; no missing row** |

## 4. Definitive comprehensiveness census

| Chapter | Frozen rows | Core formalized | Core partial | Appendix proved | Appendix unresolved / deferred | Missing | Rejected | Valid | Practice exercises out of scope |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Appetizer | 11 | 11 | 0 | 0 | 0 | 0 | 0 | 11 | 6 |
| Chapter 1 | 63 | 62 | 0 | 1 | 0 | 0 | 0 | 63 | 6 |
| Chapter 2 | 79 | 70 | 0 | 1 | 0 | 0 | 8 | 71 | 29 |
| Chapter 3 | 111 | 93 | 3 | 0 | 1 | 0 | 14 | 97 | 31 |
| Chapter 4 | 120 | 117 | 0 | 0 | 0 | 0 | 3 | 117 | 23 |
| Chapter 5 | 112 | 99 | 0 | 12 | 1 | 0 | 0 | 112 | 5 |
| Chapter 6 | 51 | 47 | 0 | 0 | 0 | 0 | 4 | 47 | 28 |
| Chapter 7 | 87 | 80 | 1 | 0 | 1 | 0 | 5 | 82 | 10 |
| Chapter 8 | 123 | 112 | 1 | 8 | 2 | 0 | 0 | 123 | 27 |
| Chapter 9 | 116 | 72 | 0 | 43 | 0 | 0 | 1 | 115 | 26 |
| **Total** | **873** | **763** | **5** | **65** | **5** | **0** | **35** | **838** | **191** |

The arithmetic checks:

- `763 + 5 + 65 + 5 = 838` valid conclusions;
- `838 + 35 = 873` frozen input rows;
- the 191 practice-exercise numbers use a separate out-of-scope denominator.

### 4.1 Full partial list

| Chapter | Book reference | Missing part |
|---|---|---|
| 3 | **Book Exercise 3.18** | Ginibre law and left/right orthogonal-multiplication instantiation |
| 3 | **Book Exercise 3.19** | actual GOE object, entry laws/independence, symmetrization calculation, and conjugation instance |
| 3 | **Book Exercise 3.20** | construction of `(Gu,Gv)` and proof that its joint law is the Gaussian product law |
| 7 | **Book Remark 7.2.1** | an extended expectation that preserves `+∞` for nonintegrable finite maxima |
| 8 | **Book equation (8.37)** | an extended-valued risk, or real risk restricted to integrable squared loss |

### 4.2 Full missing and unsure lists

- **MISSING:** none.
- **UNSURE:** none.

### 4.3 Full appendix-unresolved/deferred list

| Chapter | Book reference | Status |
|---|---|---|
| 3 | **Book Example 3.4.6**, arbitrary convex-body `ψ₁` half | deferred Borell/Brunn–Minkowski result, unused downstream |
| 5 | **Book equation (5.8)** | `APPENDIX-UNRESOLVED-002`, missing actual Riemannian geometry bridge |
| 7 | **Book §7.2.1 Brownian reflection example** | deferred external reflection-principle expectation identity |
| 8 | **Book Remark 8.6.3** | `APPENDIX-UNRESOLVED-001`, arbitrary sharp Gaussian-Chevet upper comparison |
| 8 | **Book Exercise 8.39(a–b)** | part (a) shares `APPENDIX-UNRESOLVED-001`; part (b) is proved |

### 4.4 Every final census delta

The final semantic pass changes exactly five rows from `FORMALIZED` to
`PARTIAL`:

1. Exercise 3.18;
2. Exercise 3.19;
3. Exercise 3.20;
4. Remark 7.2.1;
5. equation (8.37).

No conclusion was added or removed, so the valid denominator stays 838. The
70 appendix-owned rows are now split truthfully into 65 proved and 5
unresolved/deferred. The exhaustive list of all 35 rejected frozen rows and
the row-by-row 873-input disposition remain in `REVIEW_NOTES.md`.

## 5. Correctness verification

### 5.1 Published endpoints

`scripts/verify_readme_axioms.py` checked all **611 README rows** and **534
unique Lean endpoints**:

- 530 use exactly `[propext, Classical.choice, Quot.sound]`;
- 2 use `[propext, Quot.sound]`;
- 1 uses `[Quot.sound]`;
- 1 uses no axioms.

No endpoint uses `sorryAx` or a project-specific axiom. This proves kernel
correctness of the mapped propositions; it does not override the five
faithfulness demotions.

### 5.2 Documentation and preservation

- `scripts/audit_docstrings.py`: **5,987 / 5,987 declarations** documented
  across **101 non-appendix files**, with zero label/citation-shape errors.
- `scripts/verify_declaration_preservation.py` was rerun as requested, but its
  old-layout baseline mode exits before comparison because it requires
  pre-consolidation `ChapterN/Main.lean` imports of numbered modules; the
  final-pass start snapshot is already consolidated.
- The applicable stronger check compared every byte of all **101
  non-appendix source `.lean` files plus the package root module** against the
  frozen start snapshot: **102 compared, 0 different**. Both deterministic
  path+content hashes are
  `dfad1b2590f6c968d2790dffee11227476801d19e97d04e8dd0d9055350b7106`.
  This proves that names, statements, proofs, imports, comments, and
  docstrings outside the appendix are unchanged.
- `REVIEW_NOTES.pre-final.md` is byte-identical to the frozen pre-final
  record; both SHA-256 hashes are
  `cc0812cf5755f30f97cf65057d6a61e3c846ec45bbadb561bc5206268d272e65`.
- `REVIEW_NOTES_GPT.md` is absent; there is no stale byte-identical duplicate
  to synchronize.

### 5.3 Isolation

`HighDimensionalProbability.lean`, the consolidated chapters, Prelude, and
exercise leaves do not import `HighDimensionalProbability.Appendix` or any
module under `Appendix/`. Thus:

- no root or README-proved endpoint transitively depends on the unresolved
  Chevet placeholder;
- no main-line theorem depends on an `EXERCISE-SORRY`;
- no category-C or category-D dependency is reachable from the main line; the
  two appendix-specific unresolved registrations remain isolated.

## 6. Appendix statement-accuracy corrections

All statement changes were confined to the isolated appendix and were checked
against the original PDF.

| Target | Unfaithful former encoding | Final encoding | PDF page |
|---|---|---|---|
| Euclidean isoperimetry | `0 ≤ r`, false for `A=∅,r=0`; open thickening | `0 < r`; printed closed existential expansion | physical 151 / printed 143 |
| Spherical isoperimetry | zero cap mass allowed; open thickening | positive cap mass; closed chordal expansion | physical 152 / printed 144 |
| Gaussian isoperimetry | open-thickening variant | printed closed existential expansion | physical 154 / printed 146 |
| Talagrand convex concentration | width-one intervals and global convex/Lipschitz assumptions | support `[-1,1]^n`; cube-local assumptions | physical 158 / printed 150 |
| Special orthogonal concentration | powerset measurable space and handmade Haar premise | canonical Borel Haar law | physical 156 / printed 148 |
| Positive Ricci | unrelated metric/measure/tangent/Ricci data | genuine diffusion/Bochner implication; concrete geometry bridge explicitly unresolved | physical 156 / printed 148 |

No toolchain, vendored dependency, core, Prelude, or exercise file was changed.

## 7. Appendix target outcome

`PROVED` means source-faithful, placeholder-free, and free of `sorryAx`.
Positive Ricci is shown separately because the declaration is axiom-clean but
does not establish the PDF's concrete geometric theorem.

| # | Public declaration | Final source status | Exact axiom output |
|---:|---|---|---|
| 1 | `HDP.Chapter5.bounded_differences` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| 2 | `HDP.Chapter5.hamming_cube_concentration` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| 3 | `HDP.Chapter5.symmetric_group_concentration` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| 4 | `HDP.Chapter5.strongly_convex_density_concentration` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| 5 | `HDP.Chapter1.poisson_limit_theorem` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| 6 | `HDP.Chapter5.euclidean_isoperimetric` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| 7 | `HDP.Chapter2.berryEsseen` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| 8 | `HDP.Chapter5.talagrand_convex_concentration` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| 9 | `HDP.Chapter8.gaussianChevetUpperPrinciple_external` | `APPENDIX-UNRESOLVED-001` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| 10 | `HDP.Chapter5.spherical_isoperimetric` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| 11 | `HDP.Chapter5.gaussian_isoperimetric` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| 12 | `HDP.Chapter5.positive_ricci_concentration` | `APPENDIX-UNRESOLVED-002` (analytic implication proved) | `[propext, Classical.choice, Quot.sound]` |
| 13 | `HDP.Chapter5.special_orthogonal_concentration` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| 14 | `HDP.Chapter5.grassmannian_concentration` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| 15 | `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | PROVED | `[propext, Classical.choice, Quot.sound]` |

Final isolated appendix build:

```text
lake build HighDimensionalProbability.Appendix
PASS: 8,697 / 8,697 jobs
```

### 7.1 `APPENDIX-UNRESOLVED-001` plan: Gaussian Chevet

Two serious scalar-comparison attempts were exhausted:

1. the printed varying-radius Sudakov–Fernique hint fails: for scalar
   `u=v=1`, `w=z=1/2`, and outer radii one, the rank-one squared increment is
   `9/16`, while the separable comparison increment is `1/2`;
2. translating sets to contain zero can enlarge the radius term beyond the
   compensation supplied by Gaussian width.

Pinned Mathlib and `Pre_MatrixConcentration` have scalar Gaussian comparison
infrastructure but no vector-valued Slepian/Gordon–Chevet theorem. The viable
literature-backed route is:

1. formalize finite Gaussian block vectors and covariance contractions;
2. smooth finite maxima by log-sum-exp and justify differentiation under the
   Gaussian integral;
3. prove Khaoulani's vector-valued Slepian theorem,
   [“A Gordon–Chevet type inequality”](https://arxiv.org/abs/math/9201231);
4. apply it twice to the bilinear rank-one process to obtain the exact
   radius/width sum;
5. pass from smooth maxima to finite suprema and construct
   `GaussianChevetUpperPrinciple`.

This is a reusable but research-scale interpolation development. One tagged
placeholder remains in `Appendix/GaussianChevet.lean`, isolated from the root.

### 7.2 `APPENDIX-UNRESOLVED-002` plan: positive Ricci

The existing Bakry–Émery implication is genuine and axiom-clean. To prove the
PDF theorem:

1. add finite-dimensional smooth Riemannian manifolds, geodesic distance, and
   normalized Riemannian volume;
2. formalize Levi-Civita connection, Hessian, curvature and Ricci tensors, and
   `Ric(v,v) ≥ κ‖v‖²`;
3. construct the heat Markov semigroup and prove invariance, chain rules,
   entropy/Fisher differentiation, and long-time mixing;
4. prove the Bochner identity and package the data as
   `IsPositiveRicciRiemannianLaw`;
5. apply the already proved `positive_ricci_concentration`.

Pinned Mathlib has no complete volume/Ricci/Bochner/heat-semigroup chain for
this construction. Calling the current conditional implication “proved
positive-Ricci concentration” would violate the task's special criterion.

## 8. Prioritized correction hand-off

1. **Replace the three Chapter 3 substitutes.** Construct a genuine Ginibre
   matrix law, the GOE symmetric-matrix law and entry calculations, matrix
   left/right and conjugation isometries, and the joint law of `(Gu,Gv)`.
2. **Repair extended expectations.** Define finite maxima and population
   squared risk in `ENNReal`/`EReal`, with real-valued convenience theorems
   only under integrability. Reprove the minimizer API on the safe domain.
3. **Harden source-facing probability definitions.** Add measurable
   probability-space wrappers for scalar/vector subgaussianity and isotropy;
   use extended suprema where unboundedness is possible.
4. **Require PSD covariance publicly.** Make the Gaussian-vector source API
   reject non-PSD covariance parameters rather than inheriting Mathlib's
   Dirac totalization.
5. **Separate finite-domain real helpers from general objects.** Prefer
   `eLpNorm` and extended MGFs/expectations; keep totalized Bochner helpers
   explicitly internal or domain-qualified.
6. **Complete the two appendix bridges.** Implement vector-valued Slepian for
   Gaussian Chevet and the Riemannian geometry/heat-semigroup stack for
   positive Ricci.
## 9. Final record reconciliation

The following records now use the same figures and classifications:

- `README.md`: 611 publication mappings = 609 verified + 2 partial; exhaustive
  census 763 / 5 / 65 / 5; appendix 13 / 2;
- `REVIEW_NOTES.md`: exhaustive row-level disposition and the same census;
- `Appendix/APPENDIX_SUMMARY.md`: 13 proved / 2 unresolved with all 15 axiom
  outputs and both completion plans;
- `High_Dimensional_Probability/TranslationReport/Appendix_checkpoint.md`:
  final appendix build, target status, and verification evidence;
- this report: the definitive severity catalogue and correction hand-off.

The preserved pre-final record is `REVIEW_NOTES.pre-final.md`. There is no
`REVIEW_NOTES_GPT.md` in the live tree.
