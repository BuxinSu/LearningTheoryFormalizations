# MatrixConcentration mechanical soundness verification

> **GitHub publication scope:** this checkout contains the verification
> scripts and Markdown reports only. Raw logs, generated TSV/JSON/text
> evidence, curation inputs, transient state, and the sibling
> `TranslationReport` archive remain local. Paths to those omitted artifacts
> are retained as provenance references and are not expected to resolve here.
> The scripts are published for inspection, but a complete replay requires the
> omitted inputs; this curated checkout is not the full evidence bundle.

The full local verification archive is the permanent, reproducible evidence
bundle for the **mechanical soundness verification of the MatrixConcentration library**: the
V1–V10 audit, the UP-007 scope correction, and the post-correction
re-certification completed on 20 July 2026. This README consolidates the
complete current results in one place; this GitHub directory publishes its
scripts and Markdown reporting layer. It is written for maintainers and
skeptical third parties who want to verify the Lean library rather than trust
a summary claim. The certified toolchain is Lean 4.31.0, Lake 5.0.0, and
hash-pinned Mathlib 4.31 dependencies.

## Overall soundness statement

Conditional on the Lean 4.31 kernel and the hash-pinned Mathlib dependency,
the corrected 15-file source snapshot passed the isolated recovery-v7 build,
fresh aggregate, and standalone V6/V7/V10 checks. Every measured project declaration
uses at most `propext`, `Classical.choice`, and `Quot.sound`; the only
never-instantiated principle-like interfaces are the explicitly disclosed,
unpublished NC-Khintchine/bootstrap helpers recorded as V10-F1, not results
presented as established. The sole declared book-formalization coverage
exception is UP-007 / display (6.1.6), for which no registered Lean
counterpart is claimed. In that precise Book-to-Lean sense, the development is
comprehensive except for display (6.1.6). The fixed-point evidence chain is
complete and independently certified: the accepted terminal lifecycle run
recorded `problems=0`, `result=PASS`, a 14/14 PASS final-claims manifest, and
absent writer-lock/finalization-guard state. Certificate validity requires
both to remain absent and every covered input to remain unchanged.

## Glossary

- **`sorry` / `sorryAx`:** `sorry` is Lean's proof placeholder; compiled uses
  leave a detectable `sorryAx` dependency.
- **Axiom:** a proposition accepted without an in-library proof and therefore
  part of the logical trust assumptions.
- **Three standard axioms:** `propext`, `Classical.choice`, and `Quot.sound`,
  the only axioms permitted by this audit.
- **Kernel-checked:** elaborated proof terms were accepted by Lean's small
  trusted kernel.
- **Vacuous theorem:** a theorem whose hypotheses cannot jointly hold, or
  whose conclusion is true for an accidental trivial reason.
- **Orphan module:** a physical Lean source file not reachable from the
  library's root import and therefore absent from the root build.
- **Escape hatch:** a construct or option that could bypass ordinary checking
  or mutate the elaboration environment.
- **Trust path:** the complete chain from source declarations through
  elaboration and axioms to kernel acceptance.
- **Witness:** a named, compiled concrete example showing that hypotheses or a
  definition have nontrivial behavior.
- **Calibration:** a deliberately bad positive control proving that a scanner
  can detect the defect it is supposed to find.

## Scope and non-goals

The verified surface is the root `MatrixConcentration.lean` plus all 14 flat
modules it imports: one Prelude, eight chapters, and five appendices. The
shared file-walk universe is every `.lean` file physically below the Lake
project root, excluding exactly `.lake/**`,
`MatrixConcentration/Verification/**`, and `.audit_work/**`. Measurement found
15 files, all 15 root-reachable, no orphan, and no in-universe symlink.
Verification harnesses and planted controls under the two excluded audit
paths are inventoried separately and are never counted as library
declarations.

This folder certifies proof mechanics and the stated trust surface. It does
not independently redo book-faithfulness: statement correspondence is covered by the
[Book → Lean correspondence table](../README.md), the local project appendix
ledger `../APPENDIX_SUMMARY.md`, and the separate local `TranslationReport/`
audit trail. Those live
records explicitly exclude UP-007 / book display (6.1.6) from formal
coverage. The retained bounded
`matrix_rosenthal_pinelis_symmetric` and
`matrix_rosenthal_pinelis_centered_with_loss` results, together with their
`_aux` helpers, are support-only and are not registered correspondence
endpoints for that display. Publication
logistics such as licensing, version-control provenance, DOI assignment, and
archival are also outside this pass.

## The UP-007 scope correction

The final correction changed the formal-coverage boundary for the literal
Rosenthal–Pinelis display (6.1.6). Exactly two public leaf wrappers were
deleted:

- `matrix_rosenthal_pinelis_symmetric_integrable`, the former integrable
  leaf for symmetric inputs;
- `matrix_rosenthal_pinelis_centered_with_loss_integrable`, the former
  integrable centered-with-loss leaf.

Repository-wide source and environment searches found no in-tree caller of
either declaration, but the removal is still a public API deletion and is
recorded as such; no compatibility claim is made for downstream users outside
this repository. Four related declarations remain and were neither renamed
nor restated:

- the bounded symmetric theorem `matrix_rosenthal_pinelis_symmetric`;
- the bounded centered-with-loss theorem
  `matrix_rosenthal_pinelis_centered_with_loss`;
- the Appendix support helper
  `matrix_rosenthal_pinelis_symmetric_integrable_aux`;
- the Appendix support helper
  `matrix_rosenthal_pinelis_centered_with_loss_integrable_aux`.

These retained declarations are useful support infrastructure, but they are
not Book-correspondence endpoints for the literal display (6.1.6); in
particular, the bounded centered-with-loss result is not an exact
formalization of the centered exact-coefficient statement. Consequently
UP-007 / Book display (6.1.6) is the single declared formal-coverage
exception: the formula remains documented, and no public Lean declaration is
registered as its formal counterpart.

### Why the claim was corrected

The two removed wrappers made the public interface and correspondence
documentation look stronger than the formal result justified: their theorem
names suggested an integrable Rosenthal–Pinelis endpoint, while the
development actually supplies bounded-support reductions and conditional
Appendix machinery rather than the literal centered exact-coefficient
display. The correction is therefore a scope correction, not a new proof: it
removed the two misleading wrappers, retained and relabeled the support
declarations, registered (6.1.6) as the sole coverage exception, recomputed
every affected count, sample, dependency inventory, and report, and issued a
new certificate only after a clean fixed-point rerun. No additional Book
endpoint was invented to keep the old counts unchanged. The correction does
not show that the deleted wrappers were kernel-unsound: their proofs
compiled, and neither had an in-library caller. The defect was the public
coverage claim, and removing them prevents proof-engineering support from
being reported as a completed literal formalization.

### Correction footprint and touched-declaration checks

Because no definition body or signature changed, there was no retyping cone
to repair. The Round-1 footprint was documentation, disclosure, and linter
metadata only: `sampleCovariance`, `loewnerIcc`, `projDiag`, and `blockU`
(documentation plus targeted unused-argument metadata),
`bernoulliRepresentative` (semantic documentation), `maxSummandSq` and
`gChernoff` (boundary-disclosure documentation),
`trace_mul_conjTranspose_self` (a proof-local warning cleanup with its fully
qualified name and statement unchanged), and Chapter 7 heartbeat
option/comment maintenance. The final round then deleted exactly the two
leaf wrappers above, removed the one obsolete V6 witness that invoked a
deleted wrapper, and synchronized the source README, appendix ledger,
TranslationReport and human-verification records, and all verification
reports, curation inputs, and manifests to the one-exception policy. No
module was reorganized, and no toolchain or dependency pin changed.

[`logs/correction_touched_axioms.log`](logs/correction_touched_axioms.log)
records exactly `[propext, Classical.choice, Quot.sound]` for all eight
touched declarations that remain in the environment: `sampleCovariance`,
`trace_mul_conjTranspose_self`, `maxSummandSq`, `loewnerIcc`, `gChernoff`,
`projDiag`, `bernoulliRepresentative`, and `blockU`. The refreshed V4 census
independently establishes no axiom-set exceedance among all 2,213 project
constants and records exactly the standard three axioms for the four
retained support declarations. V3 and V5 reconfirm zero production
placeholder and zero escape hatch.

## Correction disposition and iteration log

| Round | Date | Work and outcome |
|---|---|---|
| Baseline audit | 17–18 July 2026 | The original record-only V1–V9 pass established the machine evidence chain and handed its five above-INFO findings (V9-F1, V8-F1, V8-F2, V6-F1, V6-F2) to correction as a validation worklist. |
| Round 1 | 19 July 2026 | Every worklist item was independently validated before any edit: two CONFIRMED and fixed, two REJECTED as soundness defects, one REVISED. A full fresh machine rerun passed and reached a correction fixed point without changing any theorem signature. |
| V10 re-certification | 19–20 July 2026 | The accepted record was extended with the V10 conditional-interface census, its environment inventory was reconciled with V4, and all 368 manual type-hash obligations were closed with an empty queue. |
| Final scope correction | 20 July 2026 | The two declarations that overstated formal coverage of book display (6.1.6) were removed, every affected inventory was recomputed, and the source-bound recovery-v7 build, fresh aggregate, standalone V6/V7/V10 chain, and terminal lifecycle/report gate all passed against source digest `38ffff…c89` and verification-input digest `119519…6cf`. |

### Validation ledger for the correction worklist

| Finding | Disposition | Validation evidence and minimal action |
|---|---|---|
| V9-F1 | **CONFIRMED** | Both printed commands failed from the former source-directory working directory and passed from the Lake project root. The fix was a one-line in-place README correction; no Lean declaration changed. |
| V8-F1 | **CONFIRMED** | Package lint reproduced one missing semantic docstring and four deliberately unused fidelity/API arguments. The fix added documentation and declaration-local linter annotations while retaining every argument, name, signature, and body. |
| V6-F1 | **REJECTED as a soundness defect** | All 24 handwritten theorem users of `maxSummandSq` are finite, and the compiled containment census finds no in-scope theorem reaching the unrestricted unbounded-family fallback. Only the docstring disclosure was added. |
| V6-F2 | **REJECTED as a soundness defect** | Every theorem caller either assumes a positive scale or proves a separate zero-scale branch that eliminates the coefficient; changing `gChernoff` would have retyped 43 downstream source declarations without repairing an in-scope result. Only the totalized value and analytic limit were documented. |
| V8-F2 | **REVISED** | The warning inventory is real but was never a set of soundness defects. Four uniquely local, mechanically safe diagnostics were fixed; recovery-v7 truthfully records the remaining 1,196 rows as 813 MINOR maintenance and 383 INFO style diagnostics, with zero error or missing-proof warning. |

The worklist disposition is therefore **CONFIRMED 2, REJECTED 2, REVISED 1,
DOCUMENTED-OPEN 0**. The final ten-report record contains 16 findings with
complete disposition:

- **CONFIRMED 12:** V2-F1 through V2-F4, V5-F1 through V5-F4, V6-F3, V7-F1,
  V8-F1, and V9-F1 — confirmed informational or maintenance observations,
  not remaining proof-soundness defects (the two fixed items are recorded as
  closed).
- **REJECTED as a new soundness defect 3:** V6-F1 and V6-F2 for the
  containment reasons above, and V10-F1 because the three
  NC-Khintchine/bootstrap predicates occur only in disclosed, unpublished
  conditional support infrastructure and do not back a registered result.
- **REVISED 1:** V8-F2, the classified warning inventory described above.
- **DOCUMENTED-OPEN 0.**

There are consequently **0 remaining CONFIRMED proof-soundness defects**.

The certified claims bundle comprises 14 files: this README, the ten
numbered reports, the standalone
[correction report](SOUNDNESS_CORRECTION.md), and the two frozen historical
snapshots [README.pre-correction.md](README.pre-correction.md) and
[README.pre-recertification.md](README.pre-recertification.md). The
snapshots are immutable, hash-pinned records of superseded states and carry
no current results; all current results are consolidated in this README. The
terminal lifecycle gate fails if any bundle member is missing or a frozen
snapshot drifts.

## Verification index

| # | Verification | What it guarantees | Tier | Verdict | Findings (C/M/m/I) | Report |
|---|---|---|---|---|---|---|
| V1 | Clean build integrity | All 15 project modules compile after the one permitted clean-state reset; no error or missing-proof warning appears. | machine | PASS | 0/0/0/0 | [01_build_integrity.md](01_build_integrity.md) |
| V2 | Import-graph completeness | Every physical Lean source is checked by the root build; there is no orphan module. | machine | PASS-WITH-NOTES | 0/0/0/4 | [02_import_graph.md](02_import_graph.md) |
| V3 | Placeholder census | No active missing-proof placeholder or early-stop marker exists, and no declaration depends on `sorryAx`. | machine | PASS | 0/0/0/0 | [03_sorry_audit.md](03_sorry_audit.md) |
| V4 | Universal axiom audit | Every loaded project declaration uses at most the three permitted logical axioms. | machine | PASS | 0/0/0/0 | [04_axiom_audit.md](04_axiom_audit.md) |
| V5 | Escape-hatch scan | No source construct bypasses checking or mutates the elaboration environment; benign options and local instances are inventoried. | mixed (machine scan; review classification) | PASS-WITH-NOTES | 0/0/0/4 | [05_escape_hatches.md](05_escape_hatches.md) |
| V6 | Vacuity and triviality | All 467 endpoints are classified: 433 OK, 34 SUSPECT, 0 VACUOUS. Tier C has 74 accepted rows: 40 sampled OK plus 34 boundary obligations, discharged by 54 library citations and 20 named applications. | mixed (machine Tier A/C; review Tier B) | PASS-WITH-NOTES | 0/0/0/3 | [06_vacuity_triviality.md](06_vacuity_triviality.md) |
| V7 | Definition sanity | All 51/51 measured load-bearing definitions have substantive evidence (32 direct citations and 19 compiled-witness-backed rows); 78 zero-referrer leaves (76 public and 2 private) are disclosed. | mixed (machine inventory/witnesses; review sanity judgments) | PASS-WITH-NOTES | 0/0/0/1 | [07_definition_sanity.md](07_definition_sanity.md) |
| V8 | Linter and warning pass | Package lint is clean; every fresh-build warning is classified as maintenance rather than proof unsoundness. | machine | PASS-WITH-NOTES | 0/0/1/1 | [08_linter_report.md](08_linter_report.md) |
| V9 | Published-claims cross-check | Toolchain, counts, endpoint identities, roles, axioms, commands, cleanliness, and appendix status agree with measurement. | mixed (machine claims; review record chronology) | PASS-WITH-NOTES | 0/0/0/1 | [09_readme_claims.md](09_readme_claims.md) |
| V10 | Conditional-interface census | No published result rests on an undisclosed never-discharged principle; the three unpublished conditional helpers are explicitly disclosed. | mixed (machine census; review adjudication) | PASS-WITH-NOTES | 0/0/0/1 | [10_conditional_interfaces.md](10_conditional_interfaces.md) |

`C/M/m/I` means CRITICAL / MAJOR / MINOR / INFO. A mixed verdict combines
machine evidence with the specifically named review judgment; it is not
presented as a purely automatic guarantee.

## Claims register

| Published or record-level claim | Current measurement | Status | Evidence |
|---|---|---|---|
| The library builds successfully from a clean project state. | Recovery-v7 built all 15 modules in a previously absent reserved build directory: 3,209 jobs, 15 `Built`, 0 `Replayed`, 1,196 classified warnings, zero error or missing-proof warning, and exit 0. The canonical replay covered all 15 modules with 0 `Built`, 14 `Replayed`, and exit 0. | CONFIRMED | V1 |
| The root covers all 14 inner modules. | The 15-file physical universe is 15/15 root-reachable, with no orphan or source symlink. | CONFIRMED | V2 |
| There is no `sorry`, `admit`, or unfinished proof. | Calibrated text and build-log scans find zero production placeholders; the universal axiom census finds zero `sorryAx`. | CONFIRMED | V1, V3, V4 |
| There is no `native_decide`, custom axiom, or checking bypass. | The calibrated physical-source scan finds zero bypasses, and all 2,213 current environment declarations have zero axiom-set exceedance. | CONFIRMED | V4, V5 |
| Audited endpoints use exactly the three standard axioms. | All 467 registered correspondence endpoints independently report exactly `propext`, `Classical.choice`, and `Quot.sound`. | CONFIRMED | V4, V9 |
| Public declaration counts are 467 theorems, 841 lemmas, and 135 definitions, for 1,443 total. | A comment/string-aware source recount reproduces each number; with 82 private declarations, the full measured source inventory is 1,525. | CONFIRMED | V7, V9 |
| The correspondence table has 467 rows with chapter vector 21/136/35/55/71/62/63/24. | Extraction reproduces the total and every chapter count; names, modules, and role suffixes agree 467/467, and the role partition is 401 proof endpoints plus 66 definition endpoints. | CONFIRMED | V6, V9 |
| Registered endpoints are not vacuous and load-bearing definitions are not hollow. | Standalone V6 classifies all 467 endpoints as 433 OK, 34 SUSPECT, and 0 VACUOUS. Its 74 Tier-C rows are 40 sampled plus 34 boundary obligations, with 54 library citations and 20 named applications. Standalone V7 covers all 51 load-bearing definitions with 32 citations and 19 witnesses and records 78 dead leaves (76 public, 2 private). | CONFIRMED | V6, V7 |
| No published result depends on an undisclosed never-discharged principle. | V10 reconciles 2,213/2,213 environment constants with V4; parses 1,526 text declarations into 1,531 source-backed roles; measures 3,827 source-backed theorem Prop binders, 542 normalized hashes, 368 manual hashes, and 4,762 theorem instance binders; and classifies 14 predicates as 7 PROVED, 6 CONSUMED-ONLY, and 1 DEAD, with zero queued. | CONFIRMED | V10 |
| Appendix items UP-001 through UP-006 and UP-008 have registered formal coverage; UP-007 / (6.1.6) is the sole declared exception. | There is no registered Lean counterpart for the literal UP-007 display. The retained bounded symmetric/centered-with-loss results and `_aux` helpers are support-only, non-correspondence infrastructure. | CONFIRMED | V1, V4, V9, V10 |
| The recorded toolchain is Lean/Mathlib v4.31.0. | `lean-toolchain`, Lake, the active Lean binary, and the Mathlib manifest pin agree. | CONFIRMED | V9 |
| The README commands run from the Lake project root. | Both exact printed commands exit 0 there and fail from the former source-directory working directory as the intended negative control. | CONFIRMED | V9 |
| The separate TranslationReport trail has no current open status mismatch. | Sixty-three Markdown records are chronology-checked; historical open rows are superseded by later closures. | CONFIRMED | V9 |

## Findings summary

There are 16 recorded findings: 0 CRITICAL, 0 MAJOR, 1 MINOR, and 15 INFO.
None is a remaining confirmed proof-soundness defect.

| Finding | Severity | One-line summary |
|---|---|---|
| V8-F2 | MINOR | [REVISED](08_linter_report.md): recovery-v7 contains 1,196 classified build warnings—813 maintenance rows and 383 style rows—but none is an error, missing proof, or demonstrated soundness defect. |
| V2-F1 | INFO | [Report](02_import_graph.md#v2-f1--info--stale-parent-scaffold-exists): a stale parallel scaffold outside the canonical project root is explicitly excluded. |
| V2-F2 | INFO | [Report](02_import_graph.md#v2-f2--info--sibling-name-collisions-are-excluded): the sibling currently has 10 flat Lean files, no top-level `Pre_MatrixConcentration/` or `MatrixConcentration.lean`, and two separately scoped Prelude name collisions; none enters this audit. |
| V2-F3 | INFO | [Report](02_import_graph.md#v2-f3--info--project-root-readme-is-template-boilerplate): the project-root README is repository-template boilerplate, not the library claims source. |
| V2-F4 | INFO | [Report](02_import_graph.md#v2-f4--info--audit-scratch-is-intentionally-excluded): enumerated plants and audit scratch are intentionally excluded from library counts. |
| V5-F1 | INFO | [Report](05_escape_hatches.md#v5-f1--info--benign-source-options-are-inventoried): 150 source options are resource budgets or linter settings; none disables checking. |
| V5-F2 | INFO | [Report](05_escape_hatches.md#v5-f2--info--two-narrow-reducibility-annotations): two transparent norm aliases carry narrow reducibility annotations without changing the trust path. |
| V5-F3 | INFO | [Report](05_escape_hatches.md#v5-f3--info--proof-local-instances-and-one-proved-fact): 75 proof-local instances and one proved arithmetic `Fact` were reviewed. |
| V5-F4 | INFO | [Report](05_escape_hatches.md#v5-f4--info--auto-implicit-binding-remains-enabled): default auto-implicit binding remains active; the calibrated V6 scan found no suspect Type/Prop auto-binding. |
| V6-F1 | INFO | [REJECTED](06_vacuity_triviality.md#v6-f1--info--rejected-maxsummandsq-boundary-is-outside-every-in-scope-use): the unbounded infinite-family `maxSummandSq` fallback is outside all 27 compiled direct users, including all 24 handwritten theorem users. |
| V6-F2 | INFO | [REJECTED](06_vacuity_triviality.md#v6-f2--info--rejected-gchernoff-zero-boundary-is-avoided-or-neutralized): every source user avoids or neutralizes the `gChernoff` zero-scale boundary. |
| V6-F3 | INFO | [Report](06_vacuity_triviality.md#v6-f3--info--other-totalized-semantic-boundaries-are-explicit-review-observations): 32 other explicit totalization boundaries have accepted nondegenerate evidence. |
| V7-F1 | INFO | [Report](07_definition_sanity.md#v7-f1--info--source-declarations-with-no-source-level-referrer): the corrected inventory has 78 zero-referrer leaves, comprising 76 public and 2 private declarations. |
| V8-F1 | INFO | [FIXED](08_linter_report.md): five documentation/unused-argument maintenance hits were closed; the fresh package lint is clean across 2,213 declarations (1,449 named and 764 generated) and 16 linters. |
| V9-F1 | INFO | [FIXED](09_readme_claims.md#v9-f1--info--fixed-readme-now-names-the-lake-project-root): the source README names the correct Lake project root, where both printed commands pass. |
| V10-F1 | INFO | [KNOWN-LEDGERED / REJECTED as a new soundness defect](10_conditional_interfaces.md#v10-f1--info--known-ledgered-rejected-as-a-new-soundness-defect): three never-instantiated NC-Khintchine/bootstrap helpers occur only in explicitly disclosed, unpublished conditional infrastructure and require no remediation. |

## Current certified measurements

### Declaration and correspondence counts

| Measure | Value |
|---|---:|
| Public theorems | 467 |
| Public lemmas | 841 |
| Public definitions | 135 |
| Public declarations total | 1,443 |
| All source declarations (public and private) | 1,525 |
| Book → Lean correspondence rows | 467 |
| Proof-endpoint roles | 401 |
| Definition-endpoint roles | 66 |
| Imported-environment project constants | 2,213 |

The correspondence chapter vector is `21/136/35/55/71/62/63/24`; the role
partition `401 + 66` and the chapter vector both sum to 467. The
two-declaration reduction relative to the pre-correction interface occurs in
Chapter 6. The imported-environment count and the public source-keyword
count measure different surfaces and are not expected to be equal.

### Vacuity and triviality (V6)

| Measurement | Value |
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

The equality `467 = 433 + 34 + 0` is enforced by the runner, and all 74
Tier-C obligations have endpoint-dependent evidence in the refreshed ledger.
The sample includes newly compiled, nondegenerate named applications where a
sampled endpoint lacked an existing downstream library caller; neither
deleted wrapper is sampled or used as evidence. The containment census finds
27 compiled direct users of `maxSummandSq`: 24 handwritten theorem users
(every one supplying the finite-index guard), one handwritten finite-guarded
predicate, and two generated definition helpers. The 34 SUSPECT
classifications are review-priority labels, not failed or vacuous theorems;
no registered endpoint is classified VACUOUS.

### Definition sanity (V7)

| Measurement | Value |
|---|---:|
| All source declarations | 1,525 |
| Public / private source declarations | 1,443 / 82 |
| Load-bearing definitions | 51 |
| Load-bearing definitions covered | 51 |
| Direct-citation evidence rows | 32 |
| Compiled-witness evidence rows | 19 |
| Zero-referrer leaves | 78 |
| Public / private zero-referrer leaves | 76 / 2 |

Zero-referrer status is not itself a soundness defect; it identifies
declarations that are not load-bearing for another in-library declaration.

### Conditional-interface census (V10)

| Measurement | Value |
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

The proposition-valued definition census is 14, with predicate source
statuses 7 PROVED, 6 CONSUMED-ONLY, and 1 DEAD. The persistent manual
register satisfies `368 = 359 + 9`, and its queue is empty; the independent
quality review reconciles the complete 368-hash obligation set with that
empty queue.

### Conditional support versus formal coverage

`HermitianNCKhintchineAt`, `RectangularNCKhintchineAt`, and
`ProvidesCenteredRosenthalBootstrap` are disclosed conditional interfaces:
they support internal reductions but do not supply an unconditional public
proof of the literal centered display (6.1.6). Likewise, the retained
`_integrable_aux` declarations are support helpers, not correspondence
endpoints. This distinction is the operative resolution of UP-007:
conditional or bounded support is retained honestly, while exact Book
coverage is not claimed. These interfaces are the subject of finding V10-F1.

## How to re-run

Run from the Lake project root. A plain invocation is the safe fast-resume
mode:

```sh
bash MatrixConcentration/Verification/scripts/run_all.sh
bash MatrixConcentration/Verification/scripts/run_all.sh --resume
```

Both forms append to `logs/run_all.log` and skip numbered stages with completed
`.audit_work/run_all_stages/*.done` markers. They are for resuming the same
unchanged interrupted run, not for certification.

Re-certification requires:

```sh
bash MatrixConcentration/Verification/scripts/v1_recovery_clean_build.sh
bash MatrixConcentration/Verification/scripts/run_all.sh --fresh
```

`--fresh` clears all 21 numbered stage markers and the digest-bound canonical
replay marker `.audit_work/v1_clean_build.done`. It does not clear the separate
`.audit_work/v1_recovery_build.done`: the runner either establishes clean
evidence in a designated build directory that was previously absent, or
validates the existing source/input digests, runner/config hashes, build-log
hash, unchanged canonical-tree manifests, and recovery-tree manifest before
reuse. It then re-executes the canonical replay plus V1–V5, V8, V9's machine
checks, and V10's machine census. The current V1 runners contain no recursive
deletion and never delete `.lake/build`; `.lake/packages` and `.lake/config`
are also never deleted. The run then refreshes V2, executes the ten-report
consistency check, rechecks both manifests, and writes the authoritative
[`logs/run_all.log`](logs/run_all.log) and
[`logs/run_all_status.log`](logs/run_all_status.log). The aggregate is
host-load dependent. The accepted fresh aggregate (run
`8212cc84-aad8-4abc-b0df-b68fd3241112`) passed from
`2026-07-20T17:28:34Z` to `2026-07-20T17:43:35Z` in 901 seconds, with 23
`START`, 23 `PASS`, 0 `SKIP`, 0 `FAIL`, and terminal
`ALL MACHINE STAGES PASSED`.

Review-tier judgments are preserved rather than regenerated by the aggregate:
V6 Tier B, V7 sanity adjudication, and V10 semantic adjudication. Their
machine prerequisites and curated ledgers can be checked with:

```sh
bash MatrixConcentration/Verification/scripts/v6_run.sh
bash MatrixConcentration/Verification/scripts/v7_run.sh
bash MatrixConcentration/Verification/scripts/v10_run.sh
python3 MatrixConcentration/Verification/scripts/check_consistency.py
python3 MatrixConcentration/Verification/scripts/check_final_lifecycle.py
```

The current source-bound sequence completed recovery-v7, the fresh aggregate,
and the standalone V6, V7, and V10 reruns. Recovery-v7 passed in 1,148
seconds; the aggregate passed in 901 seconds; standalone V6, V7, and V10
passed in 2,518, 240, and 143 seconds respectively.

The aggregate and standalone V1, V6, V7, and V10 runners acquire the shared,
capability-bound atomic verification-writer lock. When V1 or V10 is invoked
inside `run_all.sh`, it validates and reuses the orchestrator's outer lock
rather than acquiring a second one. A finalization guard prevents an
unauthorized writer from beginning while the final evidence sequence is
frozen.

Each numbered report gives its narrower commands, positive controls, expected
outputs, and limitations. Direct `lake env lean` harnesses pass
`-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false` because that command
does not inherit the lakefile's Lean options. The lifecycle checker is a
post-run gate: invoke it only after the explicit fresh aggregate, the
standalone V6/V7/V10 reruns, and the final record-consistency refresh are
complete. Those prerequisites were completed, and the accepted terminal
lifecycle run recorded `problems=0`, `result=PASS`, a 14/14 PASS
final-claims manifest, and clear writer-lock/finalization-guard checks. Any
later edit to a covered input or claims file requires the terminal checker
to be rerun;
[`logs/final_lifecycle_check.txt`](logs/final_lifecycle_check.txt) always
records the current gate state. The lifecycle
chronology distinguishes the historical 17 July baseline deletion from
exactly one re-certification deletion at 20 July 2026 02:49:53 EDT; the
recovery-v7 run and canonical replay both passed without deleting
`.lake/build`. A PASS certificate is valid only while both the writer lock
and finalization guard are absent.

## Faithfulness and API statement

The scope correction makes the public claim narrower and more faithful:

- it does not claim the literal centered exact-coefficient display (6.1.6);
- it preserves the bounded symmetric and centered-with-loss results;
- it preserves the Appendix integrable auxiliary reductions;
- it labels all four retained declarations according to their actual support
  role;
- it explicitly acknowledges the two-declaration public API deletion;
- it declares exactly one Book formal-coverage exception, UP-007 / (6.1.6).

Conditional on the pinned Lean/Mathlib toolchain, the completed recovery and
aggregate runs establish well-formed, kernel-accepted proof terms for the
corrected source. Kernel checking cannot by itself establish agreement with
the monograph; the correspondence and exception records supply that semantic
boundary.

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

## Environment snapshot

| Item | Recorded value |
|---|---|
| Re-certification dates | 19–20 July 2026 (EDT; UTC timestamps retained in logs) |
| Canonical root | Lake project root (the repository directory containing `lakefile.toml`) |
| Lean / Lake | Lean 4.31.0 (`68218e876d2a38b1985b8590fff244a83c321783`), Lake 5.0.0 |
| Mathlib | `inputRev = v4.31.0`, resolved revision `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| Host | macOS 15.6, Apple M2 Pro (12 cores), 16 GB memory |
| Verified source | 15 Lean files; 20 manifest-pinned source/metadata/claims inputs |
| Source-manifest top-level SHA-256 | `38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89` |
| Verification-input manifest | 147 scripts/curation/read-only-ledger inputs; SHA-256 `119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf` |
| Recovery-v7 | PASS, run `d854807a-23cd-4b3f-81f9-310c36ee9e19`, `2026-07-20T17:08:56Z`–`2026-07-20T17:28:04Z`, 1,148 seconds; 3,209 jobs, 15 `Built`, 0 `Replayed`, 1,196 warnings; log SHA-256 `9e25991ff6b5ba971442150cc369ce5d9ef24a2e726f36155435b318116d694f` |
| Fresh aggregate | PASS, run `8212cc84-aad8-4abc-b0df-b68fd3241112`, `2026-07-20T17:28:34Z`–`2026-07-20T17:43:35Z`, 901 seconds; log SHA-256 `81b8bb7fa4f415ba1f98e4f5d143390c697bce5e9474ba2464e7a39e303c30b8` |
| Standalone V6 | PASS, run `06bd42c9-8921-496e-9029-8abd8ef5c141`, `2026-07-20T17:43:57Z`–`2026-07-20T18:25:55Z`, 2,518 seconds; log SHA-256 `3314e0966da5ee4c972281e5e8f072fcbe5ba5628bea50dc623b3d985daa9f09` |
| Standalone V7 | PASS, run `ea099f89-3c20-466b-bbfb-a4e7abd839f5`, `2026-07-20T18:26:10Z`–`2026-07-20T18:30:10Z`, 240 seconds; 51/51 covered (32 citations + 19 witnesses), 78 dead leaves; log SHA-256 `1d8ab2977e077100389e2283fd79fd1abfb5f1203e8c67c3cd2814b31518b497` |
| Standalone V10 | PASS, standalone-parent run `4501a473-f8a5-49cc-93f7-6b57fe1e3fb3`, `2026-07-20T18:30:27Z`–`2026-07-20T18:32:50Z`, 143 seconds; log SHA-256 `afcfaa944f9336545621fbeb99d9008a16182495f37a9a62aefc8c28b6199adb` |
| Final lifecycle/report gate | PASS at certification (20 July 2026): `problems=0`, `result=PASS`, final claims 14/14 PASS, and absent writer lock/finalization guard; the gate must be rerun after any covered-input or claims edit, and the live log records the current state |
| Dependency mode | `.lake/packages` retained; Mathlib oleans supplied by `lake exe cache get`, not rebuilt from source |

The detailed environment is in
[`logs/environment.txt`](logs/environment.txt), per-input hashes in
[`logs/source_manifest.txt`](logs/source_manifest.txt), and final
cross-report status in
[`logs/consistency_check.txt`](logs/consistency_check.txt). The independent
final lifecycle gate is recorded in
[`logs/final_lifecycle_check.txt`](logs/final_lifecycle_check.txt), which
always reflects the most recent gate run.
