# HighDimensionalProbability verification index

## 1. Purpose and provenance

This directory records the mechanical soundness audit (Pass 06), its
finding-by-finding correction/validation pass (Pass 07) for the source
snapshot dated **2026-07-18**, and the authoritative Round 8 closure on
**2026-07-19**.  Round 8 includes a fresh two-shard exhaustive V4 replay of
the current maximal-buildable source.  The authenticated environment is Lean 4.31.0, Lake
5.0.0-src+68218e8, and Mathlib revision
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

The nine reports retain their stable finding IDs, original severities, and
coverage-sensitive verdicts.  Current dispositions are recorded separately
in the machine-readable
[Pass 07 soundness-resolution ledger](inventory/pass07_soundness_resolutions.tsv):
all 25 non-INFO findings were validated as 10 `CONFIRMED`, 14 `REVISED`, and
one `REJECTED`.  This separation preserves reproducible audit history without
presenting a frozen scope blocker or an evidence limitation as an unfixed
editable defect.

## 2. Overall soundness statement

The editable HighDimensionalProbability tree and Appendix build successfully;
the Appendix contains zero sorries, all 228 kernel `sorryAx` dependencies on the maximal
surface reconcile one-to-one with marked exercise placeholders, and the only
other axioms are `propext`, `Classical.choice`, and `Quot.sound`.  V5 finds no
unexpected escape hatch.

The maximal buildable kernel surface remains 226 of 230 expected modules.
The other four are a single failure/dependency cluster wholly inside frozen
`Pre_MatrixConcentration/`; this is an explicit out-of-scope blocker, not a
claim that it was repaired.  The Appendix registry is 14 source-faithful,
two assumption-strengthened, and one deliberately skipped result.  Two
arbitrary-set Chevet wrappers remain conditional outside the owner-selected
Q1 completion scope.  V7 now has accepted citation evidence for 231 of 300
load-bearing rows; the remaining 69 are explicit review-evidence limitations,
not demonstrated definition defects.

The authoritative fresh V4 evidence contains **15,052 declaration/axiom
rows**, the same **15,052 declaration-type rows**, **81,067 complete binder
rows**, and **1,450,620 direct type/value dependency edges**.  Its 228
`sorryAx` rows are exactly the marked exercises; Appendix has zero, and there
is no nonstandard non-`sorry` axiom.  The four absent frozen modules are not
represented as audited or proved.

## 3. Scope and terminology

| Term | Meaning in this verification bundle |
|---|---|
| Physical file | A `.lean` file under `HighDimensionalProbability/` or the real `Pre_MatrixConcentration/` tree, excluding Verification evidence. |
| Expected module | One of 228 physical modules or one of the two separate root aggregators, for 230 total. |
| Maximal buildable surface | The 224 buildable physical modules plus both root aggregators, for 226 modules in the audited kernel environment. |
| Source-faithful | The formal statement and proof disposition match the cited source obligation without an additional mathematical premise. |
| Assumption-strengthened | A proved narrower interface with an explicit premise that the repository does not derive from the source's bare assumptions. |
| Skipped | An obligation deliberately omitted from the proved registry; no theorem or placeholder is represented as its proof. |
| Out-of-scope blocker | A validated defect or coverage gap located entirely in the user-frozen `Pre_MatrixConcentration/` subtree. |
| Review-evidence limitation | No accepted citation or compiled witness currently proves nondegeneracy; this does not assert that the definition is false. |

The physical source scope is **228 files**: 214
`HighDimensionalProbability` files and 14 real `Pre_MatrixConcentration`
files.  Verification scripts, scratch harnesses, reports, and logs are
evidence surfaces, not library modules.  This work does not solve the 228
teaching exercises, edit frozen `Pre_MatrixConcentration/`, turn conditional
theorems into unconditional ones, or infer semantic faithfulness from
successful compilation alone.

Row-level faithfulness and correction evidence is in the
[faithful proofreading report](../FAITHFUL_PROOFREAD_REPORT.md), the
[correction ledger](../CORRECTION_LEDGER.md), and the
[Appendix registry](../Appendix/APPENDIX_SUMMARY.md).

## 4. V1–V9 verification index

Counts are ordered **CRITICAL / MAJOR / MINOR / INFO**.  Verdicts remain
coverage-sensitive: for example, an `INCOMPLETE` verdict can be caused by a
frozen module or an honestly retained review-evidence limitation even when
all editable source defects have been fixed.

| # | Verification | What it guarantees | Tier | Verdict | Findings (C/M/m/I) | Report |
|---|---|---|---|---|---|---|
| V1 | Build integrity | Authenticates successful editable root/Appendix builds and isolates the four-module frozen MatrixConcentration failure cluster. | Machine | ISSUES-FOUND | 0/1/1/0 | [V1 report](01_build_integrity.md) |
| V2 | Import graph | Enumerates all 228 physical files with zero unresolved local imports or cycles; the only four current orphans are the frozen failure cluster. | Machine | ISSUES-FOUND | 0/1/1/0 | [V2 report](02_import_graph.md) |
| V3 | Sorry audit | Classifies exactly 228 exercise placeholders, zero Appendix placeholders, and exact buildable-kernel reconciliation, with the frozen four-module boundary disclosed. | Mixed | INCOMPLETE | 0/1/1/1 | [V3 report](03_sorry_audit.md) |
| V4 | Axiom audit | Audits every declaration in the maximal 226-module environment and finds no project-specific axiom beyond ledgered exercise `sorryAx`. | Machine | INCOMPLETE | 0/1/0/1 | [V4 report](04_axiom_audit.md) |
| V5 | Escape-hatch audit | Finds no unexpected bypass in all 228 physical files or the named scratch universe. | Machine | PASS-WITH-NOTES | 0/0/0/4 | [V5 report](05_escape_hatches.md) |
| V6 | Vacuity and triviality | Records 14 reviewed Tier-A false positives, 784 Tier-B OK rows, two scoped Chevet limitations, and passing Tier-C suites. | Review | INCOMPLETE | 0/2/2/3 | [V6 report](06_vacuity_triviality.md) |
| V7 | Definition sanity | Dispositions all 300 load-bearing definitions: 231 have accepted citation evidence and 69 remain explicitly evidence-limited. | Review | INCOMPLETE | 0/5/0/2 | [V7 report](07_definition_sanity.md) |
| V8 | Linter report | Parses every maximal-buildable package-lint hit; only the four frozen failed modules are outside the lint environment. | Mixed | INCOMPLETE | 0/1/1/2 | [V8 report](08_linter_report.md) |
| V9 | Published-claim audit | Resolves all 540 published endpoints and verifies corrected editable records; false claims remaining in frozen MatrixConcentration stay disclosed. | Mixed | INCOMPLETE | 0/4/3/1 | [V9 report](09_readme_claims.md) |

## 5. Pass 07 resolution ledger

The 25 non-INFO findings have the following exhaustive current states:

| Current state | Count | Meaning |
|---|---:|---|
| `FIXED` | 8 | Actual editable source, audit-scope, or record defects were corrected. |
| `OUT_OF_SCOPE_BLOCKER` | 9 | The same four-module failure/publication cluster lies in frozen `Pre_MatrixConcentration/`. |
| `DOCUMENTED_SOURCE_LIMITATION` | 1 | Arbitrary-set Chevet remains conditional outside the proved, assumption-strengthened Q1 scope. |
| `REVIEW_EVIDENCE_LIMITATION` | 4 | V7 retains rows without accepted evidence; no false-definition conclusion is inferred. |
| `RESOLVED_AS_NONDEFECT` | 2 | Warning totals were duplicated log-instance counts, not unique semantic defects. |
| `NO_CHANGE` | 1 | The rejected build-recipe finding conflicts with the controlling authorized recipe. |
| **Total** | **25** | **10 confirmed + 14 revised + 1 rejected; no unclassified row.** |

## 6. Current issue and limitation register

| Cluster | Current state and consequence | Evidence |
|---|---|---|
| Exercise placeholders | Exactly 228 executable sorries occur in 228 marked exercises; the Appendix has zero.  These are allowed teaching gaps, so the entire project is not `sorryAx`-free. | [V3](03_sorry_audit.md) and [V4](04_axiom_audit.md) |
| Frozen MatrixConcentration cluster | `Appendix_RosenthalPinelis` has nine direct errors and blocks Chapters 1, 6, and 7.  Kernel/V6/V7/V8 whole-physical-surface claims therefore stop at 226/230 modules. | [V1](01_build_integrity.md) and [V2](02_import_graph.md) |
| Appendix Q1 | The finite Gaussian-Chevet result is proved with the explicit sufficient premise `0 ∈ T`.  The book's instruction to follow Theorem 7.3.1 and use Sudakov--Fernique is mathematically sound; only the old attempted scalar outer-radius comparator fails when both radii vary.  The arbitrary-set wrappers requiring `GaussianChevetUpperPrinciple` remain outside the completion claim. | [V6](06_vacuity_triviality.md) and [Appendix registry](../Appendix/APPENDIX_SUMMARY.md) |
| Appendix Q2 | Positive-Ricci concentration is proved at the explicit `RiemannianDiffusionLaw` interface, whose lower field encodes `Ric ≥ κg`, equivalently the Ricci lower bound on unit tangent vectors.  The `ψ₂` endpoints explicitly require `Measurable f` and `Integrable f μ` and cover every `L ≥ 0`, including the separately proved `L = 0` branch.  No bare Ricci-lower-bound-to-law constructor is claimed. | [Appendix registry](../Appendix/APPENDIX_SUMMARY.md) |
| Appendix Q3 | The unconditional Borell endpoint is deliberately **SKIPPED**.  Its exact proposition and a theorem conditional on a supplied Borell witness remain, but no unconditional theorem or placeholder is counted as its proof. | [Appendix registry](../Appendix/APPENDIX_SUMMARY.md) |
| Appendix Q4 | Brownian reflection is fully proved and registered source-faithfully at the finite-subfamily `extendedExpectedSupremum` interface. | [Appendix registry](../Appendix/APPENDIX_SUMMARY.md) |
| V7 semantic evidence | The final register is 231 accepted citations and 69 `UNVERIFIED_SANITY`: 29 generated/internal projections, one frozen row, and 39 substantive HDP definitions. | [V7](07_definition_sanity.md) |
| Frozen publication claims | MatrixConcentration's overbroad build and source-location claims remain false but are preserved under the freeze boundary. | [V9](09_readme_claims.md) |

The former vacuous Bernoulli helper, inert Berry–Esseen auxiliary, stale
Borell/Lipschitz keys, editable Appendix counts, doc-audit scope, and live
placeholder records are fixed.  Warning-header totals are retained only as a
maintenance signal, not as a semantic-defect count.

## 7. Findings summary

The 39 stable report rows are sorted by original severity.  There are no
CRITICAL findings; current-state detail for the 25 non-INFO rows is in the
Pass 07 ledger.

| Finding | Severity | One-line summary |
|---|---|---|
| V1-F1 | MAJOR | Revised: the four-module build failure is an explicit frozen-scope blocker; editable targets build. [V1 report](01_build_integrity.md#findings) |
| V2-F1 | MAJOR | Revised: the only four import-graph orphans are the frozen MatrixConcentration failure cluster. [V2 report](02_import_graph.md#findings) |
| V3-F1 | MAJOR | Revised: kernel reconciliation is complete on the editable surface and bounded only by the frozen four modules. [V3 report](03_sorry_audit.md#findings) |
| V4-F1 | MAJOR | Revised: exhaustive axiom coverage is 226/230 solely because the four frozen modules cannot elaborate. [V4 report](04_axiom_audit.md#findings) |
| V6-F1 | MAJOR | Revised: V6 inherits the same frozen four-module kernel/binder coverage boundary. [V6 report](06_vacuity_triviality.md#findings) |
| V6-F7 | MAJOR | Revised: the two arbitrary-set Chevet rows are a documented source/scope limitation, not part of the completed strengthened Q1. [V6 report](06_vacuity_triviality.md#findings) |
| V7-F1 | MAJOR | Revised: V7's 226/230 module boundary is wholly within frozen MatrixConcentration. [V7 report](07_definition_sanity.md#findings) |
| V7-F2 | MAJOR | Confirmed evidence limitation: shard 1 is now 51 verified and 24 unverified rows. [V7 report](07_definition_sanity.md#findings) |
| V7-F3 | MAJOR | Revised evidence limitation: shard 2 is now 56 verified and 19 unverified rows. [V7 report](07_definition_sanity.md#findings) |
| V7-F4 | MAJOR | Confirmed evidence limitation: shard 3 is now 62 verified and 13 unverified rows. [V7 report](07_definition_sanity.md#findings) |
| V7-F5 | MAJOR | Confirmed evidence limitation: shard 4 is now 62 verified and 13 unverified rows. [V7 report](07_definition_sanity.md#findings) |
| V8-F1 | MAJOR | Revised: full-physical-surface lint is blocked only by four frozen modules; editable maximal lint completes. [V8 report](08_linter_report.md#findings) |
| V9-F1 | MAJOR | Revised: false MatrixConcentration build claims are validated but frozen and explicitly out of correction scope. [V9 report](09_readme_claims.md#findings) |
| V9-F2 | MAJOR | Revised: overbroad MatrixConcentration source-location claims remain a documented frozen publication blocker. [V9 report](09_readme_claims.md#findings) |
| V9-F3 | MAJOR | Confirmed and fixed: editable HDP READMEs now state projection 768/66/4 and registry 14+2+1. [V9 report](09_readme_claims.md#findings) |
| V9-F4 | MAJOR | Confirmed and fixed: published Borell status now names the real interface and marks the unconditional endpoint skipped. [V9 report](09_readme_claims.md#findings) |
| V1-F2 | MINOR | Revised as nondefect: 7,908 is a duplicated warning-header instance count, not 7,908 distinct defects. [V1 report](01_build_integrity.md#findings) |
| V2-F2 | MINOR | Confirmed and fixed: BerryEsseenSmoothing is imported into the Appendix closure. [V2 report](02_import_graph.md#findings) |
| V3-F2 | MINOR | Confirmed and fixed: live records now state 228 exercise placeholders, zero Appendix placeholders, and 14+2+1. [V3 report](03_sorry_audit.md#findings) |
| V6-F2 | MINOR | Confirmed and fixed: the Bernoulli helper is genuinely flip-invariant and has a nonzero compiled witness. [V6 report](06_vacuity_triviality.md#findings) |
| V6-F6 | MINOR | Confirmed and fixed: explicit replacements resolve the historical Borell and Lipschitz keys. [V6 report](06_vacuity_triviality.md#findings) |
| V8-F2 | MINOR | Revised as nondefect: warning instances remain a bounded maintenance signal rather than a unique-issue count. [V8 report](08_linter_report.md#findings) |
| V9-F6 | MINOR | Revised and fixed: doc audit excludes generated Verification evidence and passes on 6,078 declarations in 101 files. [V9 report](09_readme_claims.md#findings) |
| V9-F7 | MINOR | Rejected, no change: the exact printed build recipe is authorized by the controlling task and compiles. [V9 report](09_readme_claims.md#findings) |
| V9-F8 | MINOR | Confirmed and fixed: current records distinguish historical totals from 228 live exercise and zero Appendix placeholders. [V9 report](09_readme_claims.md#findings) |
| V3-F3 | INFO | The source audit has exact 228/228 exercise-placeholder and buildable-kernel reconciliation. [V3 report](03_sorry_audit.md#findings) |
| V4-F2 | INFO | The sole project-origin opaque row is the intentional internal wrapper for `greedyOwnerIndex`, with standard axioms only. [V4 report](04_axiom_audit.md#findings) |
| V5-F1 | INFO | The 228-file scan finds no executable kernel bypass or unexpected escape hatch. [V5 report](05_escape_hatches.md#findings) |
| V5-F2 | INFO | `greedyOwnerIndex` is the sole intentional `irreducible_def`. [V5 report](05_escape_hatches.md#findings) |
| V5-F3 | INFO | Ordinary `autoImplicit` remains enabled, and V6 performs the corresponding binder check. [V5 report](05_escape_hatches.md#findings) |
| V5-F4 | INFO | Scratch hits are confined to named calibrations and audit harnesses. [V5 report](05_escape_hatches.md#findings) |
| V6-F3 | INFO | Tier A parses 7,740 declarations and dispositions all 14 current hits as reviewed false positives. [V6 report](06_vacuity_triviality.md#findings) |
| V6-F4 | INFO | Tier B records 786 reviews: 784 OK and two scoped Chevet SUSPECT rows. [V6 report](06_vacuity_triviality.md#findings) |
| V6-F5 | INFO | All three Tier-C suites pass their queue, compilation, axiom, value-edge, and planted-negative gates. [V6 report](06_vacuity_triviality.md#findings) |
| V7-F6 | INFO | The zero-reverse sweep retains 2,158 triage candidates after 2,139 documented exclusions; it is not a deletion list. [V7 report](07_definition_sanity.md#findings) |
| V7-F7 | INFO | The analyzer, calibrations, V4 joins, packet checks, and final 231/69 register validator pass. [V7 report](07_definition_sanity.md#findings) |
| V8-F3 | INFO | Maximal package lint examines 8,677 declarations and parses all 167 hits. [V8 report](08_linter_report.md#findings) |
| V8-F4 | INFO | All warning headers are parsed, but log warnings do not substitute for package lint. [V8 report](08_linter_report.md#findings) |
| V9-F5 | INFO | The dynamic audit resolves and axiom-checks all 540 unique published endpoints. [V9 report](09_readme_claims.md#findings) |

## 8. Correction iterations

Rounds 1--7 share the audit's **2026-07-18 report date**; that date is not
presented as a separate execution timestamp for each round.  In particular,
Rounds 1--5 below are marked **retrospective source-record evidence** because
no independent timestamped round logs were retained.  Rounds 2--4 unpack the
single downstream-closure block preserved in the source record without
inventing separate finding counts.  Round 8 is the actual dated follow-up on
**2026-07-19**.

| Round | Date | What was rerun or reviewed | Result | Evidence source |
|---:|---|---|---|---|
| 1 | 2026-07-18 report date; retrospective source-record evidence | Applied the foundational F-01/F-02/F-04--F-11 corrections in dependency order; revalidated F-12/F-13 and reviewed F-14. | The source record classifies the listed editable findings as fixed, F-12/F-13 as revalidated without redundant edits, and F-14 as rejected/no change. | [Final iteration history](../FINAL_CORRECTION_REPORT.md#correct--re-verify-iteration-history), [review log](../REVIEW_NOTES.md#correct--re-verify-iteration-log), and [finding ledger](../CORRECTION_LEDGER.md) |
| 2 | 2026-07-18 report date; retrospective source-record evidence | Rebuilt the first affected downstream modules after the corrected foundational definitions. | The exposed proof and elaboration breakage was repaired before the audit advanced to later consumers. | [Final iteration history](../FINAL_CORRECTION_REPORT.md#correct--re-verify-iteration-history) and [review log](../REVIEW_NOTES.md#correct--re-verify-iteration-log) |
| 3 | 2026-07-18 report date; retrospective source-record evidence | Continued the definitional-ripple review through later consumers, including the Chapter 7 and Chapter 8 cones, with statement meaning checked even where compilation succeeded. | The recorded downstream semantic review found and closed the remaining intermediate consumer obligations in that phase. | [Final iteration history](../FINAL_CORRECTION_REPORT.md#correct--re-verify-iteration-history) and [review log](../REVIEW_NOTES.md#correct--re-verify-iteration-log) |
| 4 | 2026-07-18 report date; retrospective source-record evidence | Closed the remaining downstream proof/elaboration obligations and replayed the affected whole-tree and Appendix build surfaces. | The affected surfaces returned to the green state recorded by the combined downstream-closure block. | [Final iteration history](../FINAL_CORRECTION_REPORT.md#correct--re-verify-iteration-history) and [review log](../REVIEW_NOTES.md#correct--re-verify-iteration-log) |
| 5 | 2026-07-18 report date; retrospective source-record evidence | Replayed the faithfulness review against the rendered PDF for every corrected or added statement and the five former core `PARTIAL` rows. | The source record reports no new editable faithfulness defect from this replay. | [Final iteration history](../FINAL_CORRECTION_REPORT.md#correct--re-verify-iteration-history), [review log](../REVIEW_NOTES.md#correct--re-verify-iteration-log), and [finding ledger](../CORRECTION_LEDGER.md) |
| 6 | 2026-07-18 report date | Rechecked every Pass 05 finding and all 25 non-INFO Pass 06 findings against source, generated evidence, and the owner-selected Appendix scope; replayed the build precondition. | The 25 soundness rows received exactly one disposition (10 confirmed, 14 revised, one rejected), while the Bernoulli helper, Berry--Esseen import, stale keys, records, and owner-selected Q1--Q4 outcomes were repaired or classified. | [Round 6 build](logs/pass07_round6_precondition_build.log), [resolution ledger](inventory/pass07_soundness_resolutions.tsv), and [final iteration history](../FINAL_CORRECTION_REPORT.md#correct--re-verify-iteration-history) |
| 7 | 2026-07-18 report date | Regenerated the import graph; reran V6, the completed V7 register, placeholder/documentation/README checks, whole-tree and Appendix builds, and current endpoint axiom prints. | This is retained as a retrospective pre-Round-8 source record; no independent timestamped Round 7 orchestration transcript was retained. | [Final iteration history](../FINAL_CORRECTION_REPORT.md#correct--re-verify-iteration-history), [review log](../REVIEW_NOTES.md#correct--re-verify-iteration-log), and [finding ledger](../CORRECTION_LEDGER.md) |
| 8 | 2026-07-19 | Rechecked Q1 proof provenance, Q2 Ricci normalization and function-domain boundaries, the Q3 skip, and the completed Q4 interface; replayed the whole-tree/Appendix/endpoint gates; then regenerated exhaustive V4 evidence in two Lean shards, performed the exact merge, ran the analyzer and aggregate static gate, and wrote the atomic completion manifest. | Q1 records that the book hint is sound and only the old scalar comparator failed; Q2 records `Ric ≥ κg`, explicit measurability/integrability, and every `L ≥ 0`; Q3 remains skipped; Q4 remains source-faithfully proved. Fresh V4 covers 15,052 declarations, 81,067 binders, and 1,450,620 dependency edges in 226/230 modules, with only 228 exercise `sorryAx`, zero Appendix `sorryAx`, and zero nonstandard non-`sorry` axioms. The four frozen modules remain unaudited. | [Final orchestration](logs/pass07_final_run_all.log), [whole-tree build](logs/pass07_final_whole_build.log), [Appendix build](logs/pass07_final_appendix_build.log), [Appendix axioms](logs/pass07_final_appendix_axioms.log), [shard 0](logs/pass07_v4_shard0.log), [shard 1](logs/pass07_v4_shard1.log), [merge](logs/pass07_v4_merge.log), [merge summary](logs/pass07_v4_merge_summary.json), [analysis](logs/pass07_v4_analyze.log), [aggregate static gate](logs/axiom_audit_build.log), [completion manifest](logs/pass07_v4_completion.json), and [Appendix registry](../Appendix/APPENDIX_SUMMARY.md) |

## 9. Rerunning the verification

Run from the project root:

```bash
set -o pipefail
bash HighDimensionalProbability/Verification/scripts/run_all.sh --run 2>&1 |
  tee HighDimensionalProbability/Verification/logs/run_all.log
```

Focused static validators are:

```bash
python3 -B HighDimensionalProbability/Verification/scripts/pass07_v4_completion.py --check
python3 -B HighDimensionalProbability/Verification/scripts/run_all_static_checks.py v4
python3 -B HighDimensionalProbability/Verification/scripts/check_v6_final.py
python3 -B HighDimensionalProbability/Verification/scripts/v7_definition_review.py validate --final
python3 -B HighDimensionalProbability/Verification/scripts/check_consistency.py --no-log
```

V6 and V7 are review-tier checks.  Their validators prove ledger coverage,
schema integrity, source/currentness joins, and recorded evidence contracts;
they do not mechanically recreate the human semantic judgments.
