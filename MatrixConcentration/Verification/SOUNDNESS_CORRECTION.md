# Soundness scope-correction and V1–V10 re-certification report

Date: 20 July 2026

Status: **correction applied; final fixed-point certification completed**.

Current source manifest: 20 files, SHA-256
`38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89`.
The synchronized 147-file verification-input manifest has SHA-256
`119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`.
Recovery-v7, the fresh aggregate, and standalone V6, V7, and V10 all passed
in the required order against exactly those two digests. This report records
that completed fixed-point chain. The terminal lifecycle certificate reports
14/14 live claims files stable, zero problems, and `PASS`; earlier
recovery-v6 values remain historical evidence only.

## Executive outcome

The correction changes the formal-coverage boundary for the literal
Rosenthal–Pinelis display (6.1.6). Exactly two public leaf wrappers were
deleted: the former integrable leaf for symmetric inputs and the former
integrable centered-with-loss leaf.

Both deleted declarations had no in-library callers, but their removal is
still a public API deletion and is recorded as such. No compatibility claim
is made for downstream users outside this repository.

The following related results remain:

- the bounded symmetric theorem
  `matrix_rosenthal_pinelis_symmetric`;
- the bounded centered-with-loss theorem
  `matrix_rosenthal_pinelis_centered_with_loss`;
- the Appendix support helper
  `matrix_rosenthal_pinelis_symmetric_integrable_aux`;
- the Appendix support helper
  `matrix_rosenthal_pinelis_centered_with_loss_integrable_aux`.

These retained declarations are useful support infrastructure, but they are
not Book-correspondence endpoints for the literal display (6.1.6). In
particular, the bounded centered-with-loss result is not an exact
formalization of the centered exact-coefficient statement.

Consequently, UP-007 / Book display (6.1.6) is the **single declared
formal-coverage exception**. The formula remains documented, but no public
Lean declaration is registered as its formal counterpart. All other
correspondence claims are measured relative to this explicit scope. In this
precise Book-to-Lean sense, the development is comprehensive except for
display (6.1.6).

## Why the previous claim was corrected

The two removed wrappers made the public interface and correspondence
documentation look stronger than the formal result justified. Their theorem
names suggested an integrable Rosenthal–Pinelis endpoint, while the actual
formal development supplied bounded-support reductions and conditional
Appendix machinery rather than the literal centered exact-coefficient
display.

The sound correction is therefore a scope correction, not a new proof:

1. remove the two misleading public leaf wrappers;
2. retain the mathematically useful bounded and auxiliary declarations;
3. label the retained declarations as support/non-correspondence;
4. register (6.1.6) as the sole formal-coverage exception;
5. recompute every affected count, sample, dependency inventory, and report;
6. issue a new certificate only after a clean fixed-point rerun.

No additional Book endpoint was invented to keep the old counts unchanged.

## Exact source and claims footprint

The correction touches the Chapter 6 and Appendix Rosenthal–Pinelis scope and
the records that describe it:

- Chapter 6 no longer exports the two public integrable wrappers;
- the bounded Chapter 6 theorems are retained and described as support;
- the Appendix `_integrable_aux` helpers are retained and described as
  auxiliary/non-correspondence infrastructure;
- the source README, Appendix summary, TranslationReport, correspondence
  ledger, verification scripts, and human verification log are synchronized
  to the one-exception policy;
- the obsolete V6 witness that invoked a deleted wrapper was removed;
- the deterministic Tier-C sample and evidence were refreshed;
- V7 dependency/recovery expectations and V10 environment counts were
  rebased.

No other public declaration was deleted for this correction. In particular,
the retained bounded and `_aux` declarations were not removed merely because
they are not literal Book endpoints.

The previously completed maintenance corrections concerning documentation,
lint metadata, `maxSummandSq`, `gChernoff`,
`trace_mul_conjTranspose_self`, Chapter 7 heartbeat comments, and the README
working directory remain in the tree. They are not reversed by this scope
correction.

## Validation ledger and disposition

The original correction worklist contained exactly the five above-INFO
findings inherited from the record-only pass. Each was independently
validated before any edit:

| Finding | Disposition | Validation evidence and minimal action |
|---|---|---|
| V9-F1 | **CONFIRMED** | Both printed commands failed from the former source-directory working directory and passed from the Lake project root. The fix was a one-line in-place README correction; no Lean declaration changed. |
| V8-F1 | **CONFIRMED** | Package lint reproduced one missing semantic docstring and four deliberately unused fidelity/API arguments. The fix added documentation and declaration-local linter annotations while retaining every argument, name, signature, and body. |
| V6-F1 | **REJECTED as a soundness defect** | All 24 handwritten theorem users of `maxSummandSq` are finite, and the compiled containment census finds no in-scope theorem reaching the unrestricted unbounded-family fallback. The definition and signature were left unchanged; only its fallback was disclosed in the docstring. |
| V6-F2 | **REJECTED as a soundness defect** | Every theorem caller either assumes positive scale or proves a separate zero-scale branch that eliminates the coefficient. Changing `gChernoff` would have retyped 43 downstream source declarations without repairing an in-scope result. The definition and signature were left unchanged; the totalized value and analytic limit were documented. |
| V8-F2 | **REVISED** | The 1,202-row baseline was a real warning inventory, not 1,202 soundness defects. Four uniquely local, mechanically safe diagnostics were fixed; broad warning cleanup was rejected as a non-minimal refactor. Recovery-v7 truthfully records the remaining 1,196 rows as 813 MINOR maintenance and 383 INFO style diagnostics, with zero error or missing-proof warning. |

Thus the original worklist disposition is **CONFIRMED 2, REJECTED 2,
REVISED 1, DOCUMENTED-OPEN 0**.

The final ten-report record contains 16 findings. Its complete disposition is:

- **CONFIRMED 12:** V2-F1 through V2-F4, V5-F1 through V5-F4, V6-F3,
  V7-F1, V8-F1, and V9-F1. These are confirmed informational or maintenance
  observations, not remaining proof-soundness defects.
- **REJECTED as a new soundness defect 3:** V6-F1 and V6-F2 for the
  containment reasons above, and V10-F1 because the three
  NC-Khintchine/bootstrap predicates occur only in disclosed, unpublished
  conditional support infrastructure and do not back a registered result.
- **REVISED 1:** V8-F2, as the classified warning inventory described above.
- **DOCUMENTED-OPEN 0.**

There are consequently **0 remaining CONFIRMED proof-soundness defects**.

## Minimal correction footprint

No guarded sibling was added for V6-F1 or V6-F2, and no definition body or
signature was changed. That was the smallest safe choice because the suspect
branches are contained outside registered theorem use. The declaration-level
Round-1 footprint was:

- `sampleCovariance`, `loewnerIcc`, `projDiag`, and `blockU`: documentation
  plus targeted unused-argument metadata only;
- `bernoulliRepresentative`: semantic documentation only;
- `maxSummandSq` and `gChernoff`: boundary-disclosure documentation only;
- `trace_mul_conjTranspose_self`: a proof-local warning cleanup with its
  fully qualified name and statement unchanged;
- Chapter 7 heartbeat sites: local option/comment maintenance only, with no
  theorem statement or signature change.

The final scope correction then deleted exactly two leaf declarations,
`matrix_rosenthal_pinelis_symmetric_integrable` and
`matrix_rosenthal_pinelis_centered_with_loss_integrable`. Repository-wide
source and environment searches found no in-tree caller of either. This
avoided a speculative replacement theorem and changed no downstream proof,
but it remains an intentional public API deletion for external clients. The
four retained bounded/auxiliary results listed above were not renamed or
restated.

The V9-F1 correction was confined to `MatrixConcentration/README.md`. The
records and reproducibility machinery were then synchronized: the source
README and Appendix summary, the relevant TranslationReport/HUMAN ledger
entries, the live Verification README and reports 01–10, V6/V7/V10
curation/witness inputs, manifests, and lifecycle scripts/logs. The two frozen
Verification README snapshots were not modified. No module was reorganized,
no toolchain or dependency pin changed, and no large-scale warning cleanup was
performed.

The existing source files with intentional correction edits were:

| File | Existing-declaration or record change |
|---|---|
| `Chapter1_Introduction.lean` | `sampleCovariance` documentation/linter metadata |
| `Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean` | `maxSummandSq` disclosure and the proof-local `trace_mul_conjTranspose_self` cleanup |
| `Chapter3_MatrixLaplaceTransformMethod.lean` | `loewnerIcc` documentation/linter metadata |
| `Chapter5_SumOfPSDMatrices.lean` | `gChernoff` disclosure and `projDiag`/`bernoulliRepresentative` maintenance |
| `Chapter6_SumOfBoundedRandomMatrices.lean` | deletion of the two public UP-007 leaf wrappers and support-scope documentation |
| `Chapter7_IntrinsicDimension.lean` | heartbeat option/comment maintenance |
| `Chapter8_ProofOfLiebsTheorem.lean` | `blockU` documentation/linter metadata |
| `Appendix_RosenthalPinelis.lean` | retained-helper scope documentation; no retained theorem signature changed |
| `README.md`, `APPENDIX_SUMMARY.md`, and `HUMAN_VERIFICATION_LOG.md` | commands, counts, UP-007 scope, and audit chronology |

The remaining changed files are audit records or reproducibility inputs under
`Verification/**` and the directly corresponding TranslationReport records;
they do not add a library declaration.

## Proof, dependency, and faithfulness checks for touched declarations

Because no definition body or signature changed, there was no
definition-retyping cone to repair. The potentially broad cone was nevertheless
measured before rejecting V6-F2: it contains 43 downstream source
declarations, all of whose theorem uses guard or neutralize the zero boundary.
The `maxSummandSq` containment check similarly covered every compiled direct
user and all 24 handwritten theorem users. The two removed wrappers were
leaves with no in-tree callers.

`logs/correction_touched_axioms.log` records exactly
`[propext, Classical.choice, Quot.sound]` for all eight touched declarations
that remained in the environment:

`sampleCovariance`, `trace_mul_conjTranspose_self`, `maxSummandSq`,
`loewnerIcc`, `gChernoff`, `projDiag`, `bernoulliRepresentative`, and
`blockU`.

The refreshed V4 census independently establishes no axiom-set exceedance
among all 2,213 project constants. It also records exactly the standard three
axioms for the retained support results
`matrix_rosenthal_pinelis_symmetric`,
`matrix_rosenthal_pinelis_centered_with_loss`,
`matrix_rosenthal_pinelis_symmetric_integrable_aux`, and
`matrix_rosenthal_pinelis_centered_with_loss_integrable_aux`. V3 and V5
reconfirm zero production placeholder and zero escape hatch.

The Round-1 edits did not change a mathematical statement. The proof-local
edit preserves the same theorem statement, and the documentation/metadata
edits retain the book's API hypotheses. The final deletion narrows the public
coverage claim instead of asserting a replacement formula. The closed RN/SI
faithfulness decisions were not reopened; only records whose scope/count
description changed were synchronized. UP-007 / literal display (6.1.6)
remains documented and unasserted, exactly as required.

## Correction and re-verification iterations

There were two source-changing correction → re-verification cycles, with an
intervening V10 evidence extension:

1. **Round 1 (19 July):** validate the original five-item worklist; apply the
   V9-F1 and V8-F1 maintenance fixes, the narrow V8-F2 cleanup, and the two V6
   disclosures; run the full fresh V1–V9 aggregate plus standalone V6/V7.
   The round found no new or remaining confirmed proof-soundness defect.
2. **V10 re-certification (19–20 July):** add and close the exhaustive
   conditional-interface census, including all 368 manual type-hash
   obligations and an empty queue. V10-F1 was rejected as a new defect because
   it is known-ledgered conditional support.
3. **Final scope-correction round (20 July):** remove the two misleading
   UP-007 leaf wrappers, recompute every affected declaration,
   correspondence, V6, V7, V8, V9, and V10 inventory, and execute
   recovery-v7 → fresh aggregate → standalone V6 → standalone V7 →
   standalone V10. This complete round returned zero confirmed
   proof-soundness defects and is the final fixed point.

The final whole-root target build is the recovery-v7 isolated build:
`lake build MatrixConcentration` completed 3,209 jobs, built all 15 project
modules from the previously absent reserved build directory, emitted zero
error or missing-proof warning, and exited 0. The canonical replay also exited
0 and covered all 15 modules. These results, the per-stage checks, and the
terminal lifecycle certificate are bound to the unchanged source/input digest
pair printed at the top of this report.

## Corrected declaration and correspondence counts

The deterministic source counts after the two public deletions are:

| Measure | Corrected value |
|---|---:|
| Public theorems | 467 |
| Public lemmas | 841 |
| Public definitions | 135 |
| Public declarations total | 1,443 |
| All source declarations (public and private) | 1,525 |
| Book→Lean correspondence rows | 467 |
| Proof-endpoint roles | 401 |
| Definition-endpoint roles | 66 |

The correspondence chapter vector is:

`21/136/35/55/71/62/63/24`.

Thus the role partition is `401 + 66 = 467`, and the chapter vector also sums
to 467. The two-declaration reduction occurs in Chapter 6. These counts
supersede the earlier 469-theorem, 1,445-public-declaration, 469-row,
`21/136/35/55/71/64/63/24` claims.

The imported-environment census now contains 2,213 project constants. That
environment count and the 1,443 public source-keyword count measure different
surfaces and are not expected to be equal.

## Corrected V6 result

The refreshed V6 inventories cover all 467 registered Book endpoints:

| V6 measurement | Corrected value |
|---|---:|
| Tier-B endpoints | 467 |
| OK | 433 |
| SUSPECT | 34 |
| VACUOUS | 0 |
| Tier-C evidence obligations | 74 |
| Tier-C sampled-OK obligations | 40 |
| Tier-C boundary obligations | 34 |
| Tier-C library citations | 54 |
| Tier-C named applications | 20 |
| `maxSummandSq` compiled direct users | 27 |
| `maxSummandSq` handwritten theorem users | 24 |

The equality `467 = 433 + 34 + 0` is enforced by the runner. All 74 Tier-C
obligations have endpoint-dependent evidence in the refreshed ledger:
40 sampled-OK plus 34 boundary obligations, discharged by 54 direct library
citations and 20 named applications. The sample includes newly compiled,
nondegenerate named applications where a sampled endpoint lacked an existing
downstream library caller. Neither deleted leaf is sampled or used as
evidence.

The containment census finds 27 compiled direct users of `maxSummandSq`:
24 handwritten theorem users, one handwritten finite-guarded predicate, and
two generated definition helpers. Every handwritten theorem user supplies
the finite-index guard needed to avoid the unrestricted infinite-family
fallback.

The 34 SUSPECT classifications are review-priority labels, not failed or
vacuous theorems. No registered endpoint is classified VACUOUS. Final V6 run
`06bd42c9-8921-496e-9029-8abd8ef5c141` passed all gates in 2,518 seconds
against the fixed source and verification-input digests.

## Corrected V7 result

The refreshed dependency analysis measures:

| V7 measurement | Corrected value |
|---|---:|
| All source declarations | 1,525 |
| Public / private source declarations | 1,443 / 82 |
| Load-bearing definitions | 51 |
| Load-bearing definitions covered | 51 |
| Direct-citation evidence rows | 32 |
| Compiled-witness evidence rows | 19 |
| Zero-referrer leaves | 78 |
| Public / private zero-referrer leaves | 76 / 2 |

The load-bearing set is one smaller than in the superseded round because the
formal endpoint surface changed. The 78 zero-referrer leaves consist of 76
public and two private declarations in the measured source universe.
Zero-referrer status is not itself a soundness defect; it identifies
declarations that are not load-bearing for another in-library declaration.

The definition-sanity evidence is rebased to all 51 current load-bearing
definitions, with 32 direct citations and 19 compiled witnesses. Final V7 run
`ea099f89-3c20-466b-bbfb-a4e7abd839f5` passed its inventory, witness,
chronology, and manifest gates in 240 seconds.

## Corrected V10 conditional-interface census

The current deterministic V10 measurements are:

| V10 measurement | Corrected value |
|---|---:|
| Imported project constants | 2,213 |
| Source-backed declaration roles | 1,531 |
| Parsed text declarations | 1,526 |
| Fixed-point producer rows | 46 |
| Consumer occurrences | 287 |
| Source-backed theorem proposition binders | 3,827 |
| Stable normalized proposition-binder hashes | 542 |
| Manual-review obligation hashes | 368 |
| Manual-review occurrences | 1,590 |
| Routine / discharged-by-caller adjudications | 359 / 9 |
| Remaining manual-review queue | 0 |
| Theorem instance binders | 4,762 |
| Distinct recorded instance heads | 22 |

The proposition-valued definition census remains 14, with predicate source
statuses 7 PROVED, 6 CONSUMED-ONLY, and 1 DEAD. The public scope correction
reduces the producer/consumer and binder inventories without creating an
uncurated hash. The persistent manual register remains
`368 = 359 + 9`, and its queue is empty.

The independent quality review reconciles the complete 368-hash obligation
set with an empty queue. Final V10 run
`4501a473-f8a5-49cc-93f7-6b57fe1e3fb3` passed all census, curation,
calibration, reconciliation, and fixed-input gates in 143 seconds.

### Conditional support versus formal coverage

`HermitianNCKhintchineAt`, `RectangularNCKhintchineAt`, and
`ProvidesCenteredRosenthalBootstrap` remain disclosed conditional interfaces.
They support internal reductions but do not supply an unconditional public
proof of the literal centered display (6.1.6). Likewise, the retained
`_integrable_aux` declarations are support helpers, not correspondence
endpoints.

This distinction is the operative resolution of UP-007: conditional or
bounded support is retained honestly, while exact Book coverage is not
claimed.

## Verification lifecycle state

The current isolated-recovery generation is **recovery-v7**. Any statement
that recovery-v6 is the accepted current recovery is superseded.

At this report stage:

- the corrected source and correspondence records are fixed at source digest
  `38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89`;
- all 147 verification inputs are fixed at digest
  `119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`;
- fresh recovery-v7 run `d854807a-23cd-4b3f-81f9-310c36ee9e19`
  passed in 1,148 seconds after building all 15 project modules in 3,209
  jobs, with zero error or missing-proof warning;
- fresh aggregate run `8212cc84-aad8-4abc-b0df-b68fd3241112`
  passed in 901 seconds with 23 `START`, 23 `PASS`, 0 `SKIP`, and 0 `FAIL`;
- standalone V6 run `06bd42c9-8921-496e-9029-8abd8ef5c141`,
  V7 run `ea099f89-3c20-466b-bbfb-a4e7abd839f5`, and V10 run
  `4501a473-f8a5-49cc-93f7-6b57fe1e3fb3` passed in order in 2,518,
  240, and 143 seconds respectively;
- the current V8 census has zero package-linter hits and 1,196 classified
  build warnings, comprising 813 MINOR maintenance diagnostics and 383 INFO
  style diagnostics;
- the terminal lifecycle checker accepted the synchronized live reports and
  quality evidence with 14/14 claims files stable, zero problems, and
  `result=PASS`.

The completed machine sequence and its post-report acceptance gates, from the
Lake project root, are:

```sh
bash MatrixConcentration/Verification/scripts/v1_recovery_clean_build.sh
bash MatrixConcentration/Verification/scripts/run_all.sh --fresh
bash MatrixConcentration/Verification/scripts/v6_run.sh
bash MatrixConcentration/Verification/scripts/v7_run.sh
bash MatrixConcentration/Verification/scripts/v10_run.sh
python3 MatrixConcentration/Verification/scripts/check_consistency.py
python3 MatrixConcentration/Verification/scripts/check_final_lifecycle.py
```

All commands completed in the displayed order against the same fixed
source/input pair. The aggregate's consistency stage passed before the
standalone runs, and the post-edit consistency and lifecycle checks passed
against the synchronized report bundle. Any later covered-input or claims
report edit requires the terminal checker to be rerun.

The machine logs now record:

- exact source and verification-input manifest digests;
- recovery-v7 build counts, jobs, tree hashes, and timings;
- aggregate `START`/`PASS`/`SKIP`/`FAIL` counts and completion markers;
- standalone V6/V7/V10 statuses and timings;
- final warning and linter totals;
- current report and quality-review hashes;
- absent writer-lock/finalization-guard state;
- cross-report consistency and terminal lifecycle PASS.

The terminal certificate
[`logs/final_lifecycle_check.txt`](logs/final_lifecycle_check.txt) confirms
all of these gates with `problems=0` and `result=PASS`. Its claims-bundle
digest is intentionally not copied into a claims file, which would create a
self-referential hash.

## Superseded evidence and retained history

Earlier V1–V10 evidence remains useful chronology but is not completion
evidence for the current source/input pair. In particular, old values such as
469 endpoints, 1,445 public declarations, 2,215 environment constants, 52
load-bearing definitions, and recovery-v6 are superseded.

The historical deletion events remain separately labelled:

- the original 17 July 2026 baseline deletion;
- the single 20 July 2026 re-certification deletion.

Current recovery, canonical, aggregate, and standalone runners are designed
without a deletion branch. The present correction does not authorize another
deletion of `.lake/build`.

Recovery-v2 was superseded, recovery-v3 through recovery-v5 were interrupted,
and recovery-v6 belongs to the prior certification generation. The earlier
recovery-v6 post-build `Icon\r` metadata incident remains an important
fail-closed historical event: a zero-byte macOS metadata file caused the
marker-bound recovery tree to drift, so that supervisor attempt was archived
as invalid. Its later successful recovery-v6 lifecycle is also historical
after this scope correction. Neither result is current recovery-v7 evidence.

Other archived interrupted, concurrent, resume, finalization, and stale-input
runs retain their original labels. Their bodies and chronology are not
rewritten, and no archived status is counted as a current PASS.

The frozen Verification snapshots remain unchanged:

- `README.pre-correction.md`, SHA-256
  `99d208585309890b57bc2ce542f59d8f43a33edd9ac600ebde70f8555d83fb1a`;
- `README.pre-recertification.md`, SHA-256
  `61decdc9a7d6ca489fb331159657ed63d493e4bef26bb994626bf82e262d9fe1`.

Those hashes describe frozen historical records only. They do not pin the
current live Verification README or the corrected input universe.

## Faithfulness and API statement

The scope correction makes the public claim narrower and more faithful:

- it does not claim the literal centered exact-coefficient display (6.1.6);
- it does preserve bounded symmetric and centered-with-loss results;
- it does preserve Appendix integrable auxiliary reductions;
- it labels all four retained declarations according to their actual support
  role;
- it explicitly acknowledges the two-declaration public API deletion;
- it declares exactly one Book formal-coverage exception, UP-007 / (6.1.6).

The correction does not show that the deleted wrappers were kernel-unsound.
Their proofs compiled, and neither had an in-library caller. The defect was
the public coverage claim: the wrappers were inappropriate as registered
formal endpoints for the Book display. Removing them prevents proof
engineering support from being reported as a completed literal
formalization.

Conditional on the pinned Lean/Mathlib toolchain, the completed recovery and
aggregate runs establish well-formed proof terms for the corrected source.
Kernel checking cannot by itself
establish agreement with the monograph; the correspondence and exception
records supply that semantic boundary.

## Current limitations

- The source and verification-input digests remain valid only while their
  covered inputs remain unchanged.
- V6, V7, and semantic V10 classifications include explicit review
  judgments; machine checks enforce completeness and consistency but do not
  replace mathematical interpretation.
- Zero-referrer status does not prove that a declaration is useless or
  incorrect.
- Concrete witnesses establish realizability of selected interfaces; they do
  not turn conditional support into a Book-correspondence proof.
- Cached, pinned dependencies may be retained by the recovery design; a full
  rebuild of every external dependency is outside the project-source
  certification scope.

## Acceptance criterion

The acceptance conditions are satisfied:

1. both manifests are final and stable;
2. recovery-v7 and the fresh aggregate passed;
3. standalone V6, V7, and V10 passed in order;
4. the synchronized live reports and quality review are frozen;
5. post-edit consistency and the terminal lifecycle checker report zero
   problems with no writer lock or finalization guard.

The certified conclusion is precise: the scope correction removed exactly
two misleading public wrappers, retained the bounded and auxiliary support
results, made UP-007 / Book (6.1.6) the sole declared formal-coverage
exception, and completed the replacement fixed-point certification on one
unchanged source/input pair.
