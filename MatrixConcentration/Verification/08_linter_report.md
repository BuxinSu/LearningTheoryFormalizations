# V8 — Linter and code-quality pass

**Verdict: PASS-WITH-NOTES**

**Tier: machine**

**Finding count: C=0 M=0 m=1 I=1**

## Guarantee

The soundness-scope correction removed exactly two public wrapper endpoints,
`matrix_rosenthal_pinelis_symmetric_integrable` and
`matrix_rosenthal_pinelis_centered_with_loss_integrable`. A fresh
package-scoped linter run and the isolated recovery-v7 build have now
re-established the declaration-linter and warning inventories for that
corrected snapshot.

The package scope contains **2,213 constants**: 1,449 named and 764 generated.
All 16 package linters report zero hits. The isolated clean build emits 1,196
classified quality/style warnings, comprising 813 MINOR and 383 INFO rows, with
zero errors and zero `sorry` warnings. These values come from the regenerated
current artifacts rather than from subtraction against a historical inventory.

This is a code-quality result, not a logical-soundness result. V1 and V4,
rather than V8, establish successful kernel checking and axiom discipline.

## Method

All commands ran from the project root:

```sh
python3 MatrixConcentration/Verification/scripts/source_manifest.py check
bash MatrixConcentration/Verification/scripts/v1_recovery_clean_build.sh
bash MatrixConcentration/Verification/scripts/v1_clean_build.sh
~/.elan/bin/lake env lean \
  -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false \
  MatrixConcentration/Verification/scripts/lint_package.lean \
  > MatrixConcentration/Verification/logs/v8_lint_full.log 2>&1
python3 MatrixConcentration/Verification/scripts/analyze_linters.py
```

The harness imports the root module and uses the required explicit command:

```lean
#lint in MatrixConcentration
```

The analyzer also consumes V1's `logs/build_warning_inventory.tsv`, parsed from
the authoritative isolated recovery-v7 transcript
`logs/build_full.recertification-empty-recovery.log`, not from the later
canonical replay. It emits a row-level classified inventory and aggregate
tables. Both the package-linter and warning analyses completed against source
digest
`38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89`
and verification-input digest
`119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`.

### Final V1 provenance

The authoritative **recovery-v7** run
`d854807a-23cd-4b3f-81f9-310c36ee9e19` used a newly reserved, initially empty
build directory. It ran from `2026-07-20T17:08:56Z` to
`2026-07-20T17:28:04Z` (1,148 lifecycle seconds); the timed Lake build took
1,127.02 seconds, completed 3,209 jobs, recorded 15 `Built` and 0 `Replayed`
project actions, and exited 0. The canonical build tree was byte-identical
before and after the isolated build. The build log SHA-256 is
`9e25991ff6b5ba971442150cc369ce5d9ef24a2e726f36155435b318116d694f`.

The 17 July baseline deletion is historical evidence, and exactly one
re-certification deletion occurred on 20 July in
`logs/build_delete_once.recertification.log`. Current V1 runners never delete
`.lake/build`. Recovery-v2 completed successfully but was superseded;
recovery-v3, recovery-v4, and recovery-v5 are retained only as interrupted
history and are not verdict evidence. The former recovery-v6 record, including
its metadata-drift incident and the later successful v6 run, is also retained
only as **historical, superseded evidence**. It is not evidence for the current
soundness-corrected source snapshot.

### Correction history versus this re-certification

The retained `logs/v8_lint_analysis_run.pre-correction.log` is historical pre-correction
evidence: it records five package-linter hits and 1,202 build warnings (817
MINOR, 385 INFO). The correction round closed the five declaration-linter
hits and narrowly reduced the warning inventory; it did not claim to remove
all quality warnings.

This re-certification does not inherit those historical numbers as its verdict
evidence. The authoritative current artifacts are the regenerated
`logs/v8_lint_full.log`, `logs/v8_lint_summary.txt`, and `logs/v8_*.tsv`
inventories. The fresh aggregate run
`8212cc84-aad8-4abc-b0df-b68fd3241112` ran from
`2026-07-20T17:28:34Z` to `2026-07-20T17:43:35Z` (901 seconds), recorded 23
`START` and 23 `PASS` stages with zero `FAIL` and zero `SKIP`, and exited 0.
Its run-log SHA-256 is
`81b8bb7fa4f415ba1f98e4f5d143390c697bce5e9474ba2464e7a39e303c30b8`.

### Scope calibration

The independent environment census and the fresh package-linter header
reconcile at **2,213 constants**, split into 1,449 named and 764 automatically
generated declarations. The scoped run executed 16 linters and found zero
hits. A bare `#lint` in this import-only harness would examine approximately
zero local declarations, so the analyzer rejects a missing scope header, a
scope below 1,000 declarations, or a parsed-hit count that differs from the
header.

## Results

### Package-scoped declaration linters

| Scope | Linters | Named declarations | Generated declarations | Hits |
|---|---:|---:|---:|---:|
| `MatrixConcentration` | 16 | 1,449 | 764 | 0 |

In the earlier linter-maintenance correction, five pre-correction hits were
closed as follows:

| Declaration | Correction result |
|---|---|
| `bernoulliRepresentative` | Added the missing semantic docstring. |
| `sampleCovariance` | Kept the probability-space API argument `μ`, documented why the pointwise formula does not use it, and added the targeted `unusedArguments` annotation. |
| `loewnerIcc` | Kept the book's finite-dimensional API, documented the downstream role, and added the targeted annotation. |
| `projDiag` | Kept the finite row/column-selection API, documented it, and added the targeted annotation. |
| `blockU` | Kept both finite-dimensional block indices, documented their downstream use, and added the targeted annotation. |

That earlier five-item maintenance pass did not change any name, signature,
definition body, or declaration count. This claim is deliberately limited to
that earlier pass: the current soundness-scope correction separately deleted
the two public wrapper endpoints named above.

### Clean-build warning inventory

The authoritative isolated recovery-v7 inventory contains 1,196 warnings:
813 MINOR maintenance diagnostics and 383 INFO style diagnostics. It has six
fewer rows than the 1,202-warning pre-correction baseline and two fewer rows
than the superseded recovery-v6 inventory because deleting the two wrapper
declarations removed their two local `unusedDecidableInType` diagnostics.

| Current warning class (recovery-v7) | Classification | Count |
|---|---|---:|
| `unusedDecidableInType` | MINOR | 514 |
| `unusedFintypeInType` | MINOR | 205 |
| deprecation | MINOR | 31 |
| `unusedVariables` | MINOR | 23 |
| `unusedSimpArgs` | MINOR | 17 |
| `flexible` | MINOR | 12 |
| `unnecessarySimpa` | MINOR | 6 |
| `unnecessarySeqFocus` | MINOR | 4 |
| `overlappingInstances` | MINOR | 1 |
| `unusedTactic` | MINOR | 0 |
| `style.show` | INFO | 267 |
| `style.setOption` | INFO | 62 |
| `style.longLine` | INFO | 40 |
| `style.header` | INFO | 14 |
| `style.maxHeartbeats` | INFO | 0 |
| **Total** |  | **1,196** |

The current per-module distribution is:

| Module (recovery-v7) | MINOR | INFO | Total |
|---|---:|---:|---:|
| `Prelude` | 35 | 2 | 37 |
| `Chapter1_Introduction` | 31 | 10 | 41 |
| `Chapter2_MatrixFunctionsAndProbabilityWithMatrices` | 151 | 39 | 190 |
| `Chapter3_MatrixLaplaceTransformMethod` | 58 | 31 | 89 |
| `Chapter4_MatrixGaussianAndRademacherSeries` | 106 | 65 | 171 |
| `Chapter5_SumOfPSDMatrices` | 103 | 56 | 159 |
| `Chapter6_SumOfBoundedRandomMatrices` | 93 | 52 | 145 |
| `Chapter7_IntrinsicDimension` | 0 | 35 | 35 |
| `Chapter8_ProofOfLiebsTheorem` | 65 | 31 | 96 |
| `Appendix_GoldenThompson` | 19 | 18 | 37 |
| `Appendix_GaussianConcentration` | 18 | 13 | 31 |
| `Appendix_SymmetricLowerBound` | 20 | 5 | 25 |
| `Appendix_MatrixRosenthal` | 39 | 18 | 57 |
| `Appendix_RosenthalPinelis` | 75 | 8 | 83 |
| **Total** | **813** | **383** | **1,196** |

## Findings

### V8-F1 — INFO — FIXED: five package-linter maintenance hits closed

The earlier maintenance validation confirmed one documentation omission and
four deliberately retained finite-dimensional/probability API arguments. Its
minimal correction was documentation plus declaration-local linter
annotations; it did not delete a faithfulness/API parameter. The fresh
scope-corrected package run reconfirms zero hits across all 16 linters and all
2,213 declarations. This was not a proof-soundness finding. Separately, the
soundness correction intentionally deleted two public wrapper endpoints; that
deletion is not part of this five-item maintenance claim.

### V8-F2 — MINOR — REVISED: 1,196 classified quality warnings remain

The historical 1,202-row inventory was real but was not 1,202 soundness
defects. Four uniquely local, mechanically justified warnings were fixed, and
the now-superseded recovery-v6 build recorded 1,198 classified rows. The
current recovery-v7 build records 1,196 rows: 813 MINOR and 383 INFO. The
calibrated build audit confirms that none is an error or `sorry` warning.

The earlier decision against broad non-minimal cleanup remains part of the
historical rationale. The exact current category counts above come from the
fresh row-level inventory and its analyzer-generated summaries.

## Raw evidence

- [`logs/v8_lint_full.log`](logs/v8_lint_full.log) — final package-scoped
  `#lint` output and 2,213-declaration scope header; SHA-256
  `1664768eb970269b1c738b1873bd11d32dd2f58b96313c6347ad979526bb8466`.
- [`logs/v8_package_lint.tsv`](logs/v8_package_lint.tsv) — header-only
  zero-hit declaration-linter inventory.
- [`logs/v8_package_lint_by_linter.tsv`](logs/v8_package_lint_by_linter.tsv)
  and [`logs/v8_package_lint_by_module.tsv`](logs/v8_package_lint_by_module.tsv)
  — package-lint summaries.
- [`logs/v8_build_warnings_classified.tsv`](logs/v8_build_warnings_classified.tsv)
  — all 1,196 recovery-v7 warning rows with severity classification; SHA-256
  `5eeee26e9dafa3ce0157e70dd068666687771ff79dd44e6ddc0d5348b675c439`.
- [`logs/build_warning_inventory.tsv`](logs/build_warning_inventory.tsv) — V1's
  row-level isolated-clean-build warning input before V8 severity
  classification.
- [`logs/v8_build_warnings_by_class.tsv`](logs/v8_build_warnings_by_class.tsv)
  and [`logs/v8_build_warnings_by_module.tsv`](logs/v8_build_warnings_by_module.tsv)
  — build-warning summaries.
- [`logs/v8_lint_summary.txt`](logs/v8_lint_summary.txt) — validated final
  counts and scope-calibration PASS; SHA-256
  `5a4b3b1b7b51022e9e153be99b80b23bcf3d907c8e2613dc63c7270e38e42844`.
- [`logs/run_all.log`](logs/run_all.log) — orchestrated-stage exit status and
  analyzer summary output from the 23/23 PASS fresh aggregate.
- [`logs/build_full.recertification-empty-recovery.log`](logs/build_full.recertification-empty-recovery.log)
  and
  [`logs/build_full.recertification-empty-recovery.status.log`](logs/build_full.recertification-empty-recovery.status.log)
  — recovery-v7 empty-build transcript and digest-bound PASS status.
- [`logs/v1_canonical_build_before.tsv`](logs/v1_canonical_build_before.tsv)
  and [`logs/v1_canonical_build_after.tsv`](logs/v1_canonical_build_after.tsv)
  — identical inventories of the untouched canonical build tree across the
  isolated recovery build.
- [`logs/final_evidence_supervisor.log`](logs/final_evidence_supervisor.log)
  and
  [`logs/final_evidence_supervisor_status.log`](logs/final_evidence_supervisor_status.log)
  — retained earlier supervisor chronology, not the current corrected-source
  acceptance record.
- [`logs/final_lifecycle_check.txt`](logs/final_lifecycle_check.txt) — the
  independent terminal acceptance gate for lifecycle and report
  reconciliation; the final run reports zero problems, `result=PASS`, 14/14
  final claims present, and every writer-lock/finalization-guard gate PASS.
- [`logs/source_manifest.txt`](logs/source_manifest.txt) — source files,
  configuration inputs, per-file hashes, and final top-level digest
  `38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89`.
- [`logs/verification_input_manifest_summary.txt`](logs/verification_input_manifest_summary.txt)
  — 147 verification inputs with final digest
  `119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`.

The retained [`logs/v8_lint_analysis_run.pre-correction.log`](logs/v8_lint_analysis_run.pre-correction.log)
is the explicitly historical pre-correction analyzer result; it is not an
input to the current verdict.

## Limitations

The current result is limited to the 16 linters reported by the pinned
Lean/Mathlib/Batteries environment and the warnings enabled by the project's
Lake options. Linters are heuristic and stylistic: a clean linter result does
not establish theorem meaning, while a linter hit alone does not imply
unsoundness.

The single-file `lake env lean` invocation does not inherit the lakefile's
linter set; that is why this report combines the explicit package-scoped
`#lint` run with the V1 warning inventory produced by `lake build`.

Most importantly, a clean linter result is structurally blind to conditional
proof interfaces. A kernel-valid theorem of shape `P → Q` can lint cleanly
even when the library never constructs `P`; named `Prop`-valued interfaces
such as the disclosed NC-Khintchine/bootstrap conditions therefore cannot be
certified by V8. Consequently, V8's zero-hit result must not be read as
evidence that every theorem hypothesis is discharged.
