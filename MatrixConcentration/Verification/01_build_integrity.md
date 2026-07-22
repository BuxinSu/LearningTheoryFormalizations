# V1 — Build integrity from a clean state

**Verdict: PASS**

**Tier: machine**

**Finding count: C=0 M=0 m=0 I=0**

## Guarantee

The V1 gate requires the root `MatrixConcentration` target and all 14
transitively imported source modules to elaborate successfully under Lean
4.31.0 in a previously absent, atomically reserved empty root-package build
directory. It also requires a separate successful canonical `.lake/build`
replay and zero errors or `sorry` warnings in both logs. Recovery-v7 and the
subsequent canonical replay both pass on the corrected source snapshot. The
independent final lifecycle checker subsequently passed with zero problems,
14/14 final-claims files, and no writer lock or finalization guard present.

## Method

The reproducible commands, run from the Lake project root, are:

```sh
python3 MatrixConcentration/Verification/scripts/source_manifest.py check
python3 MatrixConcentration/Verification/scripts/verification_input_manifest.py check
bash MatrixConcentration/Verification/scripts/v1_recovery_clean_build.sh
bash MatrixConcentration/Verification/scripts/v1_clean_build.sh
bash MatrixConcentration/Verification/scripts/compile_calibration_plants.sh
python3 MatrixConcentration/Verification/scripts/audit_build_logs.py
```

The isolated recovery runner checks both pinned manifests and the dedicated
Lake configuration, records the canonical `.lake/build` content tree, then
atomically reserves the previously absent real directory
`.audit_work/v1_recertification_recovery_build_v7`. After:

```sh
~/.elan/bin/lake exe cache get
```

it requires that reserved directory to remain real and empty and runs:

```sh
~/.elan/bin/lake \
  --file MatrixConcentration/Verification/scripts/v1_recovery_lakefile.toml \
  --rehash --no-cache --no-ansi build MatrixConcentration
```

The dedicated Lake file differs from the live `lakefile.toml` only by its
top-level `buildDir`. The runner requires the canonical tree manifest to be
byte-identical before and after this build, hashes the completed recovery tree,
and binds the source/input digests, runner/config/checker hashes, build-log
hash, both canonical manifests, and recovery-tree manifest in a structured
completion marker. Any pre-existing output without that marker is rejected
rather than deleted, reused, or overwritten. The v2 recovery completed
successfully but was superseded after verification inputs changed. Interrupted
v3, v4, and v5 directories remain preserved as failed chronology. The
previously accepted v6 completion is now also superseded by the soundness
correction. Recovery-v7 is the current accepted generation.

The canonical runner is deliberately incapable of deleting a build directory.
It refreshes the dependency cache and runs:

```sh
~/.elan/bin/lake --no-ansi build MatrixConcentration
```

under the same capability-bound writer lock. A fresh aggregate clears only its
digest-bound canonical replay marker. The accepted aggregate validated and
reused the independent v7 clean evidence, then executed this canonical replay
again.

Historically, after the superseded v6 build, a zero-byte macOS `Icon\r`
metadata file appeared in the recovery output. The first aggregate reuse
attempt detected that post-build tree drift and failed closed. Its evidence
was archived; the then-accepted v6 recovery directory hierarchy was made
non-writable, and its marker-bound content tree was restored exactly before
the superseded supervisor reused it. This chronology is retained as incident
evidence, not as current v7 completion evidence.

Deletion history is recorded separately: the 17 July 2026 baseline deletion is
historical prior-round evidence, and exactly one re-certification deletion
occurred at 20 July 2026 02:49:53 EDT. The historical isolated v6 build and
the current V1 runner design perform no deletion of `.lake/build`,
`.lake/packages`, or `.lake/config`.

### Empty-result calibration

The `sorry`-warning parser was calibrated by compiling
`.audit_work/SorryPlant.lean`, which contains one public and one private theorem
closed by `sorry`. Lean emitted two “declaration uses `sorry`” warnings, and the
same parser detected both. It detected zero such warnings in both the current
recovery-v7 isolated build and its canonical replay.
See
[`logs/calibration_sorry_compile.log`](logs/calibration_sorry_compile.log) and
[`logs/build_audit_summary.txt`](logs/build_audit_summary.txt).

## Results

The current source snapshot has source-manifest SHA-256
`38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89`.
The accepted verification-input digest is
`119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`.

Recovery-v7 run `d854807a-23cd-4b3f-81f9-310c36ee9e19` ran from
`2026-07-20T17:08:56Z` to `2026-07-20T17:28:04Z` (1,148 lifecycle
seconds). Its timed root build completed 3,209 jobs in 1,127.02 seconds with
exit status 0. The log records all 15 project module actions as `Built` (15
`Built`, 0 `Replayed`), including the explicit `MatrixConcentration` root
action, and ends with `Build completed successfully (3209 jobs)`. Its SHA-256
is `9e25991ff6b5ba971442150cc369ce5d9ef24a2e726f36155435b318116d694f`;
the structured completion-marker SHA-256 is
`83693c18446dcc62cb6d66ffd91fa2bcedf879857bb95d3a06e7ec322bb5b8b3`.
The canonical before/after manifests are byte-identical and each has SHA-256
`e69f732a100b22128536e2f9ce6a9072e00a0267d1fe872d4470453dac74a962`;
the completed recovery-tree manifest SHA-256 is
`33758604c7282c3b1b3adb66cf545a585bd54c4b29d29dc3a20c3f5e57a2689f`.

Aggregate run `8212cc84-aad8-4abc-b0df-b68fd3241112` validated that clean
evidence in two seconds, then ran the canonical replay in 7.19 seconds. The
aggregate ran its 21 numbered stages plus the final V2 refresh and consistency
check: 23 `START`, 23 `PASS`, zero `FAIL`, and zero `SKIP`, from
`2026-07-20T17:28:34Z` to `2026-07-20T17:43:35Z` (901 seconds), with exit
status 0. Its log SHA-256 is
`81b8bb7fa4f415ba1f98e4f5d143390c697bce5e9474ba2464e7a39e303c30b8`.
The replay records 0 `Built` and the exact 14 non-root modules as `Replayed`;
the explicit root target is inferred
from the requested command and the unique 3,209-job success terminal. It also
exits 0 with no error or `sorry` warning. Its log SHA-256 is
`2d00b188e9bd4f1ea2ffcc2e6bb1492e71aabe4fb7749087e980264e54cecdff`.

| Group | Modules covered |
|---|---|
| Foundation | `MatrixConcentration.Prelude` |
| Chapters | `Chapter1_Introduction`, `Chapter2_MatrixFunctionsAndProbabilityWithMatrices`, `Chapter3_MatrixLaplaceTransformMethod`, `Chapter4_MatrixGaussianAndRademacherSeries`, `Chapter5_SumOfPSDMatrices`, `Chapter6_SumOfBoundedRandomMatrices`, `Chapter7_IntrinsicDimension`, `Chapter8_ProofOfLiebsTheorem` |
| Appendices | `Appendix_GoldenThompson`, `Appendix_GaussianConcentration`, `Appendix_SymmetricLowerBound`, `Appendix_MatrixRosenthal`, `Appendix_RosenthalPinelis` |

The calibrated parser reports:

| Check | Recovery-v7 isolated build | Current canonical replay |
|---|---:|---:|
| Expected modules covered | 15 / 15 | 15 / 15 |
| Explicit `Built` / `Replayed` project actions | 15 / 0 | 0 / 14 |
| Root target | explicitly `Built` | inferred from command and success terminal |
| Build errors | 0 | 0 |
| Build `sorry` warnings | 0 | 0 |
| Other warnings | 1,196 | 1,196 |
| Calibration `sorry` warnings detected | 2 / 2 | 2 / 2 |

Every current recovery-v7 non-`sorry` warning is preserved with file, line,
class, and message in
[`logs/build_warning_inventory.tsv`](logs/build_warning_inventory.tsv), with
the file/class aggregation in
[`logs/build_warning_summary.tsv`](logs/build_warning_summary.tsv). V8
classified all 1,196 as maintenance/style diagnostics rather than build or
proof failures: 813 MINOR and 383 INFO.

All five appendix modules named in `APPENDIX_SUMMARY.md` §6 appeared among the
successful recovery-v7 module actions. V3–V5 independently check the corrected
snapshot's placeholder, axiom, and escape-hatch claims.

## Findings

None.

## Raw evidence

- [`logs/build_full.recertification-empty-recovery.log`](logs/build_full.recertification-empty-recovery.log)
  and
  [`logs/build_full.recertification-empty-recovery.status.log`](logs/build_full.recertification-empty-recovery.status.log)
  — current recovery-v7 isolated clean build: 15 `Built`, 0 `Replayed`, 3,209
  jobs, state PASS, exit 0, and hash-bound provenance.
- [`logs/cache_get.recertification-empty-recovery.log`](logs/cache_get.recertification-empty-recovery.log),
  [`logs/v1_recovery_config_check.log`](logs/v1_recovery_config_check.log),
  [`logs/v1_canonical_build_before.tsv`](logs/v1_canonical_build_before.tsv),
  [`logs/v1_canonical_build_after.tsv`](logs/v1_canonical_build_after.tsv), and
  [`logs/v1_recovery_build_tree.tsv`](logs/v1_recovery_build_tree.tsv) —
  dependency-cache, exact-config, canonical noninterference, and recovery-tree
  evidence.
- [`logs/v1_recovery_reuse_status.log`](logs/v1_recovery_reuse_status.log) —
  aggregate-time validation of the recovery-v7 clean evidence.
- [`logs/build_full.log`](logs/build_full.log) — current canonical
  replay: 0 `Built`, 14 `Replayed`, inferred root target, 3,209 jobs, exit 0.
- [`logs/cache_get.log`](logs/cache_get.log) — canonical replay cache refresh.
- [`logs/build_delete_once.log`](logs/build_delete_once.log) — historical
  17 July baseline deletion plus no-delete canonical replay chronology.
- [`logs/build_delete_once.recertification.log`](logs/build_delete_once.recertification.log)
  — exactly one re-certification deletion at 20 July 2026 02:49:53 EDT plus
  its no-delete resumes; it is not an action of the current runners.
- [`logs/build_full.recertification-empty-recovery-v2.log`](logs/build_full.recertification-empty-recovery-v2.log)
  and
  [`logs/build_full.recertification-empty-recovery-v2.status.log`](logs/build_full.recertification-empty-recovery-v2.status.log)
  — successful but superseded v2 recovery evidence.
- The `invalid-v3-interrupted`, `invalid-v4-interrupted`, and
  `invalid-v5-interrupted` recovery artifacts and retained audit build
  directories are incomplete chronology, never completion evidence.
- [`logs/build_full.recertification-empty-recovery.invalid-v6-postbuild-icon-drift-20260720T095109Z.log`](logs/build_full.recertification-empty-recovery.invalid-v6-postbuild-icon-drift-20260720T095109Z.log)
  and
  [`logs/run_all.invalid-v6-postbuild-icon-drift-20260720T095109Z.log`](logs/run_all.invalid-v6-postbuild-icon-drift-20260720T095109Z.log)
  — archived fail-closed metadata-drift attempt; the then-accepted v6 recovery
  directory hierarchy was made non-writable, and its marker-bound content tree
  was restored exactly before superseded reuse.
- [`logs/build_audit_summary.txt`](logs/build_audit_summary.txt) — parsed
  clean/canonical coverage, provenance, errors, actions, and calibrated `sorry`
  result.
- [`logs/build_warning_inventory.tsv`](logs/build_warning_inventory.tsv) and
  [`logs/build_warning_summary.tsv`](logs/build_warning_summary.tsv) — complete
  non-`sorry` warning inventory.
- [`logs/run_all.log`](logs/run_all.log) and
  [`logs/run_all_status.log`](logs/run_all_status.log) — current aggregate run
  `8212cc84-aad8-4abc-b0df-b68fd3241112`, 23/23 logged stage blocks, PASS/0.
- [`logs/final_evidence_supervisor_status.log`](logs/final_evidence_supervisor_status.log)
  — superseded recovery-v6 supervisor chronology, retained as historical
  evidence only.
- [`logs/final_lifecycle_check.txt`](logs/final_lifecycle_check.txt) — linked
  terminal lifecycle/report acceptance certificate: `problems=0`,
  `result=PASS`, final claims manifest 14/14, and lock/guard checks clear.
- [`logs/verification_input_manifest.tsv`](logs/verification_input_manifest.tsv)
  and [`logs/verification_input_manifest_summary.txt`](logs/verification_input_manifest_summary.txt)
  — 147 pinned verification/curation/read-only-ledger inputs; top digest
  `119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`.

## Limitations

This verifies a clean rebuild of all project code against cached, hash-pinned
dependencies (`.lake/packages` retained; Mathlib oleans from
`lake exe cache get`); a from-scratch dependency build was not performed, and
dependency integrity rests on the lake-manifest.json pins.

Build success establishes elaboration and kernel checking, not mathematical
meaning, theorem nonvacuity, definition substance, or absence of undischarged
principle-like interfaces; V6, V7, and V10 check those questions separately.
