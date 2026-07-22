# MatrixConcentration mechanical soundness verification

This folder is the permanent, self-contained evidence bundle for the
**mechanical soundness verification pass for the MatrixConcentration
library**, run on 17–18 July 2026 with Lean 4.31.0, Lake 5.0.0, and Mathlib
v4.31.0. It is intended for maintainers and skeptical third parties who want
to distinguish kernel-level soundness evidence (V1–V9 here) from the separate
book-faithfulness audit.

## Overall soundness statement

Conditional on the correctness of the Lean 4.31 kernel and the pinned Mathlib 4.31 dependency, the certified 15-file source snapshot rebuilds cleanly, and no audited declaration depends on an axiom outside the standard set `propext`, `Classical.choice`, and `Quot.sound`; no unfinished proof, custom axiom, trust bypass, vacuous main theorem, or hollow load-bearing definition was found. The audit did find two contained public-definition boundary defects, code-quality and API-leaf observations, and a source-README working-directory error; these exceptions are documented below and do not weaken the kernel-checked proofs.

## Glossary

- **`sorry` / `sorryAx`:** Lean's placeholder for a missing proof and the
  axiom it introduces into the trusted result.
- **Axiom:** an assumed proposition with no proof inside the checked
  development.
- **The three standard axioms:** `propext`, `Classical.choice`, and
  `Quot.sound`, the only logical axioms permitted by this audit.
- **Kernel-checked:** accepted by Lean's small trusted proof checker after
  elaboration.
- **Vacuous theorem:** a formally true theorem whose hypotheses cannot be met,
  or whose conclusion is true for an irrelevant degenerate reason.
- **Orphan module:** a shipped Lean file that the root build never imports and
  therefore may never check.
- **Escape hatch:** syntax or an option that weakens, bypasses, or mutates the
  normal checking path.
- **Trust path:** the chain from source statement and proof through elaboration
  to the Lean kernel and declared axioms.
- **Witness:** a named, compiled example showing that premises or a definition
  have a concrete nondegenerate use.
- **Calibration:** a deliberately bad planted input proving that a detector
  can find the defect it reports absent from production source.

## Scope and non-goals

The verified source surface is the root `MatrixConcentration.lean` module and
all 14 flat modules it imports: one Prelude, eight chapters, and five
appendices. V2 measured all 15 as root-reachable, with zero orphans and zero
in-universe symlinks.

The shared file-walk universe is every `.lean` file physically below the
project root, excluding exactly `.lake/**`,
`MatrixConcentration/Verification/**`, and `.audit_work/**`. The last path is
audit scratch: V2 enumerates its controls and harnesses separately rather than
silently ignoring them. The source README and appendix ledger are not compiled
source, but both are pinned by the source manifest and checked in V9.

This folder does **not** certify that the Lean statements faithfully translate
Tropp's monograph. That separate claim is documented by the
[Book → Lean correspondence table](../README.md), the
[appendix ledger](../APPENDIX_SUMMARY.md), and the
[TranslationReport audit trail](../../../TranslationReport/SOURCE_FAITHFULNESS_LEDGER.md).
V9 checks those records only for project-status and chronology consistency.

## Verification index

| # | Verification | What it guarantees | Tier | Verdict | Findings (C/M/m/I) | Report |
|---|---|---|---|---|---|---|
| V1 | Clean build integrity | All 15 project modules compile after the one permitted clean-state reset; no error or missing-proof warning appears. | machine | PASS | 0/0/0/0 | [01_build_integrity.md](01_build_integrity.md) |
| V2 | Import-graph completeness | Every physical Lean source is checked by the root build (no orphan module). | machine | PASS-WITH-NOTES | 0/0/0/4 | [02_import_graph.md](02_import_graph.md) |
| V3 | Placeholder census | No active missing-proof placeholder or early-stop marker exists, and no declaration depends on `sorryAx`. | machine | PASS | 0/0/0/0 | [03_sorry_audit.md](03_sorry_audit.md) |
| V4 | Universal axiom audit | Every loaded project declaration uses at most the three permitted logical axioms. | machine | PASS | 0/0/0/0 | [04_axiom_audit.md](04_axiom_audit.md) |
| V5 | Escape-hatch scan | No source construct bypasses checking or mutates the elaboration environment; benign options and local instances are inventoried. | mixed (machine lexical scan; review classification of reducibility and local-instance/`Fact` hits) | PASS-WITH-NOTES | 0/0/0/4 | [05_escape_hatches.md](05_escape_hatches.md) |
| V6 | Vacuity and triviality | All 469 published endpoints were reviewed, none was vacuous, and all 34 suspects plus 40 stratified samples have accepted endpoint-dependent evidence. | mixed (Tier A/C machine; Tier B review) | PASS-WITH-NOTES | 0/0/2/1 | [06_vacuity_triviality.md](06_vacuity_triviality.md) |
| V7 | Definition sanity | All 52 measured load-bearing definitions have substantive citation or compiled-witness evidence (no hollow definition). | mixed (inventory/compilation machine; sanity judgments review) | PASS-WITH-NOTES | 0/0/0/1 | [07_definition_sanity.md](07_definition_sanity.md) |
| V8 | Linter and warning pass | Package-wide linters and every clean-build warning were captured and classified as code quality, not proof soundness. | machine | PASS-WITH-NOTES | 0/0/2/0 | [08_linter_report.md](08_linter_report.md) |
| V9 | Published-claims cross-check | Toolchain, counts, endpoint identities/roles/axioms, cleanliness, and appendix status were measured against the published records. | mixed (claims checks machine; record chronology review) | ISSUES-FOUND | 0/1/0/0 | [09_readme_claims.md](09_readme_claims.md) |

`C/M/m/I` means CRITICAL / MAJOR / MINOR / INFO. A mixed-tier verdict
combines machine evidence with the explicitly identified review judgment; it
is not equivalent to a wholly machine-decided result.

## Claims register

| Published or record-level claim | Measurement | Status | Evidence |
|---|---|---|---|
| The library builds cleanly. | A one-time clean build completed 3,209 jobs, built 15/15 modules, and had zero errors or `sorry` warnings. | CONFIRMED | V1 |
| The root covers 14 inner modules. | The 15-file universe is 15/15 root-reachable, with no orphan or source symlink. | CONFIRMED | V2 |
| There is no `sorry`, `admit`, or other unfinished proof. | Calibrated text/build scans found zero production placeholders; the universal axiom census found zero `sorryAx`. | CONFIRMED | V1, V3, V4 |
| There is no `native_decide`, custom axiom, or checking bypass. | The calibrated physical-source scan found zero bypasses, and 2,215 environment declarations had zero axiom-set exceedances. | CONFIRMED | V4, V5 |
| Audited endpoints use exactly the three standard axioms. | All 469 correspondence endpoints resolve and independently report exactly `propext`, `Classical.choice`, and `Quot.sound`; V4 proves the stronger at-most-three result universally. | CONFIRMED | V4, V9 |
| Public declaration counts are 469 theorems, 841 lemmas, and 135 definitions, for 1,445 total. | A comment/string-aware source recount reproduced all four numbers. | CONFIRMED | V9 |
| The correspondence table has 469 rows with chapter vector 21/136/35/55/71/64/63/24. | Extraction reproduced the total and every chapter count. | CONFIRMED | V6, V9 |
| Correspondence names, final modules, and `thm`/`lem`/`def` roles are current. | Agreement is 469/469 for each field; the role split is 299/104/66. | CONFIRMED | V9 |
| Appendix items UP-001 through UP-008 are closed, except the explicitly unasserted literal UP-007 formula. | All nine named proof declarations resolve with the exact standard axiom set; all five appendix modules built. | CONFIRMED | V1, V4, V9 |
| The recorded toolchain is Lean/Mathlib v4.31.0. | `lean-toolchain`, Lake, the active Lean binary, and the Mathlib manifest pin agree. | CONFIRMED | V9 |
| The README commands run “From this directory.” | Both printed commands fail from the source-README directory and succeed from the Lake project root. | CONTRADICTED | V9-F1 |
| The separate TranslationReport trail has no current open status mismatch. | Sixty-three Markdown records were checked chronologically; 14 historical open rows are superseded by later closures. | CONFIRMED | V9 |

## Findings summary

There are no CRITICAL findings. Findings are sorted by severity:

| Finding | Severity | One-line summary |
|---|---|---|
| V9-F1 | MAJOR | [Report](09_readme_claims.md#v9-f1--major--readme-build-commands-name-the-wrong-working-directory): the source README says to run two commands from its own directory, but both work only from the parent Lake project root. |
| V6-F1 | MINOR | [Report](06_vacuity_triviality.md#v6-f1--minor--maxsummandsq-collapses-unbounded-index-families-to-zero): `maxSummandSq` maps an unbounded infinite-index family to the real-supremum fallback value zero; current handwritten users are finite or finite-guarded. |
| V6-F2 | MINOR | [Report](06_vacuity_triviality.md#v6-f2--minor--gchernoff-uses-the-wrong-totalized-value-at-l--0): `gChernoff θ 0` totalizes to zero instead of the removable analytic limit `θ`; audited theorem callers avoid or neutralize that boundary. |
| V8-F1 | MINOR | [Report](08_linter_report.md#v8-f1--minor--five-package-linter-issues): package lint found one undocumented helper and four declarations with unused arguments. |
| V8-F2 | MINOR | [Report](08_linter_report.md#v8-f2--minor--clean-build-carries-1202-quality-warnings): the clean build has 1,202 classified non-`sorry` quality/style warnings: 817 MINOR and 385 INFO rows. |
| V2-F1 | INFO | [Report](02_import_graph.md#v2-f1--info--stale-parent-scaffold-exists): a stale parallel MatrixConcentration scaffold exists at the parent workspace and was excluded. |
| V2-F2 | INFO | [Report](02_import_graph.md#v2-f2--info--stale-sibling-copies-exist): stale MatrixConcentration copies exist inside the sibling project and were excluded. |
| V2-F3 | INFO | [Report](02_import_graph.md#v2-f3--info--project-root-readme-is-template-boilerplate): the project-root README is repository-template boilerplate, not the library claims source. |
| V2-F4 | INFO | [Report](02_import_graph.md#v2-f4--info--audit-scratch-is-intentionally-excluded): calibration plants and harnesses under `.audit_work/` are enumerated but excluded from library counts. |
| V5-F1 | INFO | [Report](05_escape_hatches.md#v5-f1--info--benign-source-options-are-inventoried): all 149 source options are heartbeat budgets or linter settings, with no checking-disabling option. |
| V5-F2 | INFO | [Report](05_escape_hatches.md#v5-f2--info--two-narrow-reducibility-annotations): two reducibility annotations expose bundled norm aliases and do not alter the trust path. |
| V5-F3 | INFO | [Report](05_escape_hatches.md#v5-f3--info--proof-local-instances-and-one-proved-fact): 75 proof-local instances and one proved arithmetic `Fact` were contextually reviewed. |
| V5-F4 | INFO | [Report](05_escape_hatches.md#v5-f4--info--auto-implicit-binding-remains-enabled): Lean's default `autoImplicit = true` remains active; V6 found zero suspect single-letter Type/Prop auto-binds. |
| V6-F3 | INFO | [Report](06_vacuity_triviality.md#v6-f3--info--other-totalized-semantic-boundaries-are-explicit-review-observations): the other 32 SUSPECT endpoints expose explicit totalized boundaries but have nondegenerate models and accepted endpoint-dependent evidence. |
| V7-F1 | INFO | [Report](07_definition_sanity.md#v7-f1--info--source-declarations-with-no-source-level-referrer): 77 repository-local API leaves have no source referrer after excluding only 403 deliberately terminal theorem endpoints. |

## How to re-run

Run from the Lake project root. The machine-tier orchestrator is
manifest-gated, staged, and re-entrant; completed stages have markers under
`.audit_work/run_all_stages/`, while the final V2 scratch refresh and
README/report consistency check always rerun:

```sh
nohup bash MatrixConcentration/Verification/scripts/run_all.sh \
  > MatrixConcentration/Verification/logs/run_all_launcher.log 2>&1 &
```

The script also writes the authoritative
[`logs/run_all.log`](logs/run_all.log). The delivered snapshot was exercised
end-to-end from a clean shell and ended with `ALL MACHINE STAGES PASSED`.
The original clean V1 build measured 232.79 seconds on the recorded host; the
final warmed, re-entrant machine orchestrator measured 4 minutes 34 seconds.
Collector and linter times depend on the state of the pinned cache, so use
these as host-specific expectations rather than portable bounds.

Primary per-check entry points are:

| Check | Re-run command from the project root |
|---|---|
| Check V1 | `bash MatrixConcentration/Verification/scripts/v1_clean_build.sh && bash MatrixConcentration/Verification/scripts/compile_calibration_plants.sh && python3 MatrixConcentration/Verification/scripts/audit_build_logs.py` |
| Check V2 | `python3 MatrixConcentration/Verification/scripts/import_graph.py` |
| Check V3 | `python3 MatrixConcentration/Verification/scripts/scan_placeholders.py calibration && python3 MatrixConcentration/Verification/scripts/scan_placeholders.py production && python3 MatrixConcentration/Verification/scripts/reconcile_sorry_axioms.py` |
| Check V4 | Follow the version check, calibrated Lean collector, and analyzer recipe in [V4 Method](04_axiom_audit.md#method). |
| Check V5 | `python3 MatrixConcentration/Verification/scripts/scan_escape_hatches.py calibration && python3 MatrixConcentration/Verification/scripts/scan_escape_hatches.py production` |
| Check V6 | `bash MatrixConcentration/Verification/scripts/v6_run.sh` |
| Check V7 | `bash MatrixConcentration/Verification/scripts/v7_run.sh` |
| Check V8 | Follow the package-scoped `#lint` command and analyzer recipe in [V8 Method](08_linter_report.md#method); the Lean command is expected to return nonzero for the recorded hits. |
| Check V9 | Follow the extraction, endpoint collector, fake-name calibration, command test, and chronology recipe in [V9 Method](09_readme_claims.md#method). |

The exact flags and output paths are in each linked report. V6 Tier B is a
469-row mathematical close reading, and V7's nondegeneracy rationales are
review judgments: their ledgers and coverage can be machine-validated, but
the judgments themselves are not push-button. V9's record-chronology
interpretation also contains a light review component.

## Environment snapshot

| Item | Recorded value |
|---|---|
| Run dates | 17–18 July 2026 (EDT; UTC timestamps retained in logs) |
| Canonical root | `/Users/buxinsu/My_Drive/Research/AI4Math/Learning_formalization/MatrixConcentration` |
| Lean / Lake | Lean 4.31.0 (`68218e876d2a38b1985b8590fff244a83c321783`), Lake 5.0.0 |
| Mathlib | `inputRev = v4.31.0`, resolved revision `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| Host | macOS 15.6, Apple M2 Pro (12 cores), 16 GB memory |
| Verified source | 15 Lean files; 20 manifest-pinned source/metadata/claims inputs |
| Source-manifest top-level SHA-256 | `fed91763188507cfe348d1346bc3f63a0a4096b3a33836951898e272f07713c1` |
| Dependency mode | `.lake/packages` retained; Mathlib oleans supplied by `lake exe cache get`, not rebuilt from source |

All verdicts in this folder apply only to the source snapshot with top-level
digest `fed91763188507cfe348d1346bc3f63a0a4096b3a33836951898e272f07713c1`.
The full capture is in [`logs/environment.txt`](logs/environment.txt), the
per-file hashes in [`logs/source_manifest.txt`](logs/source_manifest.txt), and
the final cross-report result in
[`logs/consistency_check.txt`](logs/consistency_check.txt).
