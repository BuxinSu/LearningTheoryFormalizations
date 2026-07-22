# MatrixConcentration mechanical soundness verification

This directory is the permanent evidence bundle for the V1–V9 mechanical
soundness audit and the July 2026 final-correction pass for the
`MatrixConcentration` Lean library. It separates kernel-level soundness
evidence from the already completed book-faithfulness review.

The correction disposition, exact source footprint, iteration history, and
final fixed-point evidence are consolidated in the
[soundness-correction report](SOUNDNESS_CORRECTION.md).

## Overall soundness statement

Conditional on the Lean 4.31 kernel and the pinned Mathlib 4.31 dependency,
the corrected 15-file source tree builds successfully. The calibrated audits
find no `sorry`/`admit`, `sorryAx`, custom axiom, checking bypass, vacuous
published endpoint, or hollow load-bearing definition. Every audited
declaration uses at most `propext`, `Classical.choice`, and `Quot.sound`, and
all 469 published endpoints use exactly those three standard axioms.

The correction worklist leaves zero confirmed soundness defects. The README
working-directory error and five package-linter maintenance hits were fixed.
The two flagged totalized-definition boundaries were independently contained
to out-of-scope or neutralized uses and rejected as soundness defects, with
their behavior disclosed in source documentation. The corrected build has a
1,198-row warning inventory: 815 rows are classified MINOR maintenance and
383 INFO style observations. These inventory rows were never established as
1,198 soundness defects, and none is a proof failure.

## Scope and non-goals

The verified source surface is `MatrixConcentration.lean` and all 14 flat
modules it imports: one Prelude, eight chapters, and five appendices. V2
measures all 15 as root-reachable, with no orphan or in-universe symlink.

The shared source universe is every `.lean` file below the Lake project root,
excluding exactly `.lake/**`, `MatrixConcentration/Verification/**`, and
`.audit_work/**`. Verification harnesses and calibration plants are recorded
separately and are not library declarations.

This bundle does not redo the source-faithfulness audit. That separate result
is recorded in the [Book → Lean correspondence table](../README.md), the
[appendix ledger](../APPENDIX_SUMMARY.md), and the
[TranslationReport trail](../../../TranslationReport/SOURCE_FAITHFULNESS_LEDGER.md).
The documented literal UP-007 formula remains intentionally unasserted and
was not changed by this pass.

## Verification index

| # | Verification | What it guarantees | Tier | Verdict | Findings (C/M/m/I) | Report |
|---|---|---|---|---|---|---|
| V1 | Clean build integrity | All 15 project modules compile after the one permitted clean-state reset; no error or missing-proof warning appears. | machine | PASS | 0/0/0/0 | [01_build_integrity.md](01_build_integrity.md) |
| V2 | Import-graph completeness | Every physical Lean source is checked by the root build; there is no orphan module. | machine | PASS-WITH-NOTES | 0/0/0/4 | [02_import_graph.md](02_import_graph.md) |
| V3 | Placeholder census | No active missing-proof placeholder or early-stop marker exists, and no declaration depends on `sorryAx`. | machine | PASS | 0/0/0/0 | [03_sorry_audit.md](03_sorry_audit.md) |
| V4 | Universal axiom audit | Every loaded project declaration uses at most the three permitted logical axioms. | machine | PASS | 0/0/0/0 | [04_axiom_audit.md](04_axiom_audit.md) |
| V5 | Escape-hatch scan | No source construct bypasses checking or mutates the elaboration environment; benign options and local instances are inventoried. | mixed | PASS-WITH-NOTES | 0/0/0/4 | [05_escape_hatches.md](05_escape_hatches.md) |
| V6 | Vacuity and triviality | All 469 endpoints were reviewed; all 34 suspects and 40 stratified samples have accepted endpoint-dependent evidence. | mixed | PASS-WITH-NOTES | 0/0/0/3 | [06_vacuity_triviality.md](06_vacuity_triviality.md) |
| V7 | Definition sanity | All 52 measured load-bearing definitions have substantive citation or compiled-witness evidence. | mixed | PASS-WITH-NOTES | 0/0/0/1 | [07_definition_sanity.md](07_definition_sanity.md) |
| V8 | Linter and warning pass | Package lint is clean; every corrected-build warning is classified as maintenance rather than proof soundness. | machine | PASS-WITH-NOTES | 0/0/1/1 | [08_linter_report.md](08_linter_report.md) |
| V9 | Published-claims cross-check | Toolchain, counts, endpoint identities/roles/axioms, commands, cleanliness, and appendix status agree with measurement. | mixed | PASS-WITH-NOTES | 0/0/0/1 | [09_readme_claims.md](09_readme_claims.md) |

`C/M/m/I` means CRITICAL / MAJOR / MINOR / INFO. Mixed-tier reports combine
machine evidence with the explicitly documented review judgment.

## Claims register

| Published or record-level claim | Measurement | Status | Evidence |
|---|---|---|---|
| The library builds successfully from a clean project state. | The one-time clean build completed 3,209 jobs, covered 15/15 modules, and had zero errors or `sorry` warnings; the corrected root target also builds green. | CONFIRMED | V1 |
| The root covers 14 inner modules. | The 15-file universe is 15/15 root-reachable, with no orphan or source symlink. | CONFIRMED | V2 |
| There is no `sorry`, `admit`, or unfinished proof. | Calibrated text/build scans found zero production placeholders; the universal axiom census found zero `sorryAx`. | CONFIRMED | V1, V3, V4 |
| There is no `native_decide`, custom axiom, or checking bypass. | The calibrated physical-source scan found zero bypasses, and all 2,215 environment declarations had zero axiom-set exceedances. | CONFIRMED | V4, V5 |
| Audited endpoints use exactly the three standard axioms. | All 469 correspondence endpoints independently report exactly `propext`, `Classical.choice`, and `Quot.sound`. | CONFIRMED | V4, V9 |
| Public declaration counts are 469 theorems, 841 lemmas, and 135 definitions, for 1,445 total. | A comment/string-aware source recount reproduced all four numbers. | CONFIRMED | V9 |
| The correspondence table has 469 rows with chapter vector 21/136/35/55/71/64/63/24. | Extraction reproduced the total and every chapter count. | CONFIRMED | V6, V9 |
| Correspondence names, final modules, and `thm`/`lem`/`def` roles are current. | Agreement is 469/469 for each field; the role split is 299/104/66. | CONFIRMED | V9 |
| Appendix items UP-001 through UP-008 are closed, except the explicitly unasserted literal UP-007 formula. | All nine named proof declarations resolve with the exact standard axiom set; all five appendix modules build. | CONFIRMED | V1, V4, V9 |
| The recorded toolchain is Lean/Mathlib v4.31.0. | `lean-toolchain`, Lake, the active Lean binary, and the Mathlib manifest pin agree. | CONFIRMED | V9 |
| The README commands run from the Lake project root. | Both exact printed commands exit 0 from the documented project root; both fail from the former source-directory cwd as the intended negative control. | CONFIRMED | V9 |
| The separate TranslationReport trail has no current open status mismatch. | Sixty-three Markdown records were checked chronologically; 14 historical open rows are superseded by later closures. | CONFIRMED | V9 |

## Correction disposition and iteration log

The frozen pre-correction verification index is preserved verbatim and left
untouched in [README.pre-correction.md](README.pre-correction.md).

| Round | Date | Work and outcome |
|---|---|---|
| Baseline | 17–18 July 2026 | The record-only V1–V9 pass reported 1 MAJOR, 4 MINOR, and 10 INFO findings. The correction worklist was V9-F1, V6-F1/F2, and V8-F1/F2. |
| Round 1 | 19 July 2026 | Validated all five above-INFO findings: CONFIRMED 2 (V9-F1, V8-F1), REJECTED 2 (V6-F1, V6-F2), REVISED 1 (V8-F2), DOCUMENTED-OPEN 0. All ten original INFO items were revalidated with no upgrade. After the minimal corrections, the final `--fresh` machine run executed all 20 numbered stages plus the final V2 refresh and consistency check: 22 START, 22 PASS, 0 SKIP, and terminal `ALL MACHINE STAGES PASSED`. Clean report-specific V6 and V7 reruns also passed. No new or remaining CONFIRMED soundness defect was found, so this single correction → re-verification round reached the required fixed point on digest `58ed2f65409638c932843eb547e71575dd49108e2ffaeffaa6888cdcf1ee4b30`. |

Two failed intermediate runs are retained only as chronology:

- [`logs/run_all.pre-correction.log`](logs/run_all.pre-correction.log) used
  intermediate digest `3a966451…` and reached V1 log audit, where the former
  parser incorrectly treated Lake's `Replayed` action as no module action.
- [`logs/run_all.round1-attempt1.log`](logs/run_all.round1-attempt1.log) used
  final digest `58ed2f65…`, completed environment capture, the root build,
  calibration generation/compilation, and V1 audit, then failed V2 because
  the former scratch-file check rejected an unexpected macOS `Icon\r`
  audit-scratch artifact.

Neither archive is completion evidence. The authoritative clean output is
[`logs/run_all.log`](logs/run_all.log).

The two rejected items are not silently dropped:

- V6-F1's unbounded infinite-family fallback is real, but its 29 compiled
  direct users are exactly 26 handwritten theorem users (all with `Fintype`),
  one handwritten finite-guarded predicate, and two generated definition
  helpers. No in-scope result reaches the flagged branch.
- V6-F2's `gChernoff θ 0 = 0` totalization is real. Its dependency cone has
  44 declarations including `gChernoff`; all 43 downstream source declarations
  either require a positive scale or neutralize the zero-scale coefficient.
  No in-scope conclusion is corrupted.

## Findings summary

There are no CRITICAL or MAJOR findings and no remaining confirmed soundness
defect.

| Finding | Severity | One-line summary |
|---|---|---|
| V8-F2 | MINOR | [REVISED](08_linter_report.md#v8-f2--minor--revised-1198-classified-quality-warnings-remain): the corrected build's 1,198-row warning inventory contains 815 MINOR maintenance and 383 INFO style rows; the rows are an inventory, not 1,198 prior soundness defects. |
| V2-F1 | INFO | [Report](02_import_graph.md#v2-f1--info--stale-parent-scaffold-exists): a stale parallel scaffold outside the canonical root was excluded. |
| V2-F2 | INFO | [Report](02_import_graph.md#v2-f2--info--stale-sibling-copies-may-exist): stale copies in a sibling project are inventoried and excluded. |
| V2-F3 | INFO | [Report](02_import_graph.md#v2-f3--info--project-root-readme-is-template-boilerplate): the project-root README is template boilerplate, not the library claims source. |
| V2-F4 | INFO | [Report](02_import_graph.md#v2-f4--info--audit-scratch-is-intentionally-excluded): enumerated audit scratch is intentionally excluded from library counts. |
| V5-F1 | INFO | [Report](05_escape_hatches.md#v5-f1--info--benign-source-options-are-inventoried): all 150 options are resource budgets or linter settings; none disables checking. |
| V5-F2 | INFO | [Report](05_escape_hatches.md#v5-f2--info--two-narrow-reducibility-annotations): two reducibility annotations expose bundled norm aliases without changing the trust path. |
| V5-F3 | INFO | [Report](05_escape_hatches.md#v5-f3--info--proof-local-instances-and-one-proved-fact): 75 proof-local instances and one proved arithmetic `Fact` were reviewed. |
| V5-F4 | INFO | [Report](05_escape_hatches.md#v5-f4--info--auto-implicit-binding-remains-enabled): default auto-implicit binding remains active; V6 found no suspect Type/Prop auto-bind. |
| V6-F1 | INFO | [REJECTED](06_vacuity_triviality.md#v6-f1--info--rejected-maxsummandsq-boundary-is-outside-every-in-scope-use): the unbounded infinite-family fallback is outside every finite or finite-guarded source use. |
| V6-F2 | INFO | [REJECTED](06_vacuity_triviality.md#v6-f2--info--rejected-gchernoff-zero-boundary-is-avoided-or-neutralized): all source users avoid or neutralize the zero-scale boundary. |
| V6-F3 | INFO | [Report](06_vacuity_triviality.md#v6-f3--info--other-totalized-semantic-boundaries-are-explicit-review-observations): 32 other explicit boundaries have accepted nondegenerate evidence. |
| V7-F1 | INFO | [Report](07_definition_sanity.md#v7-f1--info--source-declarations-with-no-source-level-referrer): 77 repository-local API leaves have no source referrer after terminal theorem endpoints are excluded. |
| V8-F1 | INFO | [FIXED](08_linter_report.md#v8-f1--info--fixed-five-package-linter-maintenance-hits-closed): five documentation/unused-argument maintenance hits were closed without changing any signature; package lint reports 0 hits across 2,215 declarations and 16 linters. |
| V9-F1 | INFO | [FIXED](09_readme_claims.md#v9-f1--info--fixed-readme-now-names-the-lake-project-root): the README names the correct Lake project root, where both printed commands pass. |

## How to re-run

The authoritative final round ran from the Lake project root with:

```sh
bash MatrixConcentration/Verification/scripts/run_all.sh --fresh
```

`--fresh` is also the default. It clears all numbered stage markers and forces
the root build while preserving the one-time `.lake/build` deletion marker;
it rewrites [`logs/run_all.log`](logs/run_all.log). `--resume` appends and
reuses completed markers, so it is only for the same interrupted run with
unchanged verification code and is never the final evidence mode.

V6 Tier B and V7's nondegeneracy judgments have report-specific rerun
commands. Their completed status is recorded in
[`logs/v6_run.log`](logs/v6_run.log),
[`logs/v6_run_status.log`](logs/v6_run_status.log), and
[`logs/v7_run_status.log`](logs/v7_run_status.log):

```sh
bash MatrixConcentration/Verification/scripts/v6_run.sh
bash MatrixConcentration/Verification/scripts/v7_run.sh
```

Primary report-specific commands and limitations appear in each report.
In particular, V8's corrected package-scoped `#lint` run reports zero hits.

## Environment snapshot

| Item | Recorded value |
|---|---|
| Run dates | 17–19 July 2026 (EDT; UTC timestamps retained in logs) |
| Canonical root | `/Users/buxinsu/My_Drive/Research/AI4Math/Learning_formalization/MatrixConcentration` |
| Lean / Lake | Lean 4.31.0 (`68218e876d2a38b1985b8590fff244a83c321783`), Lake 5.0.0 |
| Mathlib | `inputRev = v4.31.0`, resolved revision `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| Host | macOS 15.6, Apple M2 Pro (12 cores), 16 GB memory |
| Verified source | 15 Lean files; 20 manifest-pinned source/metadata/claims inputs |
| Source-manifest top-level SHA-256 | `58ed2f65409638c932843eb547e71575dd49108e2ffaeffaa6888cdcf1ee4b30` |
| Dependency mode | `.lake/packages` retained; Mathlib oleans supplied by `lake exe cache get`, not rebuilt from source |

All current verdicts apply only to the source snapshot with top-level digest
`58ed2f65409638c932843eb547e71575dd49108e2ffaeffaa6888cdcf1ee4b30`.
The full environment capture is in
[`logs/environment.txt`](logs/environment.txt), per-file hashes in
[`logs/source_manifest.txt`](logs/source_manifest.txt), and final cross-report
status in [`logs/consistency_check.txt`](logs/consistency_check.txt).
