# V1 — Build integrity from a clean state

**Verdict: PASS-WITH-NOTES**

The complete verified surface elaborates with zero errors from a certified
copy that had no `.lake/build` directory before the two-build sequence. The final
fixed-point replay builds the combined `HighDimensionalProbability
MatrixConcentration` target and the deliberately root-isolated
`HighDimensionalProbability.Appendix` target. Both commands exit zero. V2
independently establishes that the file-walk universe has no orphan modules,
so no additional module-target build is required.

## Scope and method

The count-dependent source scope uses the common file-walk universe: every
physical `.lean` file below the HDP source directory
`HighDimensionalProbability/` union every physical `.lean` file below the
real project-root `MatrixConcentration/` directory, excluding
`HighDimensionalProbability/Verification/**` and `.lake/**`.  The project-root
`HighDimensionalProbability.lean` aggregator is handled separately.
`tmp/*.lean` and `.audit_work/**/*.lean` are separately enumerated scratch,
not library source.  V2 proves that these 222 physical library files are all
selected by the build surfaces exercised here.

The current clean-build commands were run from:

`/private/tmp/hdp_final_clean_project_bca641_20260721`

That copy contains the current HDP source, MatrixConcentration source, root
aggregator, and three pin files. It retains pinned dependency packages via a
`.lake/packages` link but contains no project `.lake/build` artifacts. Its
independently generated manifest has the same 226 entries and digest
`bca641bd4c523754aa472b97cb1ed5638a6eb7361f99158a3f231a03a7446460`
as the active tree.

The exact current clean-state sequence was:

1. verify that `.lake/build` is absent and record
   `logs/final_clean_copy_builddir_absence.log`;
2. generate the temp-copy source manifest and record
   `logs/final_clean_copy_manifest_round10.log`;
3. `~/.elan/bin/lake build HighDimensionalProbability MatrixConcentration`;
4. `~/.elan/bin/lake build HighDimensionalProbability.Appendix`.

The manifest, absence check, and builds were wrapped by
`HighDimensionalProbability/Verification/scripts/run_logged.py`; their raw
logs include the command, working directory, timestamps, elapsed time, and
exit status. The historical cache and one-use cleanup logs remain useful setup
provenance, but they are not relabeled as evidence for the Round-10 digest.
Two superseded attempts are likewise not evidence:
`build_full_final_clean_20260721.log` used a Lake override that did not move
the build root, and `build_full_final_clean_copy_20260721.log` was canceled
after the still-live documentation defect was discovered. Only the two
`*_recertification.log` build transcripts named below control V1.

## Results

| Surface | Raw log | Exit | Elapsed (s) | Result |
|---|---|---:|---:|---|
| certified-copy source manifest | `logs/final_clean_copy_manifest_round10.log` | 0 | 0.381 | 226 entries; digest matches the active tree |
| certified-copy build-directory absence | `logs/final_clean_copy_builddir_absence.log` | 0 | 0.006 | `.lake/build` absent before the two-build sequence |
| `HighDimensionalProbability` + glob-built `MatrixConcentration` | `logs/build_full_recertification.log` | 0 | 3,573.196 | 8,671 jobs; success; zero error headers |
| isolated `HighDimensionalProbability.Appendix` closure | `logs/build_appendix_recertification.log` | 0 | 3,270.547 | 8,701 jobs; success; zero error headers |

`logs/v1_build_recertification_summary.log` mechanically checks the two exit
codes, zero error-header counts, one-time-clean marker, warning profile, and
Appendix registry/summary reconciliation.  Its final gate is `PASS`.

The primary evidence is the [certified-copy manifest](logs/final_clean_copy_manifest_round10.log),
[initial build-directory absence check](logs/final_clean_copy_builddir_absence.log),
[combined clean build](logs/build_full_recertification.log),
[isolated Appendix build](logs/build_appendix_recertification.log), and
[machine summary](logs/v1_build_recertification_summary.log).

## Warning inventory

`scripts/warning_inventory.py` parsed every warning header in both
module-target build logs.  The complete source-located table (file, line,
class, count, and originating build log) is in
[the warning inventory](logs/warning_inventory_recertification.log).

| Build log | Warning-header instances | `sorry` instances | Other warning instances |
|---|---:|---:|---:|
| `build_full_recertification.log` | 1,915 | 228 | 1,687 |
| `build_appendix_recertification.log` | 2,461 | 0 | 2,461 |
| **Total** | **4,376** | **228** | **4,148** |

The 228 `sorry` warnings are exactly the expected exercise-leaf declarations:
V3 maps them declaration-by-declaration to the in-source exercise markers,
and V4 confirms the same set through `sorryAx`.  There is no `sorry` warning
in the Appendix or MatrixConcentration surface.  The remaining instances are
72 deprecations and 4,076 linter/style diagnostics. Lake can replay warnings
for dependencies, so these are log instances, not necessarily distinct
source defects.  Both inventory inputs were produced by `lake build` with the
lakefile's linter options active; the exact README `lake env lean` checks used
by V9 are intentionally not mixed into this inventory.

Relative to the pre-removal comparison, full-build warnings changed from
1,918 to 1,915, Appendix warnings from 2,464 to 2,461, total warnings from
4,382 to 4,376, non-`sorry` warnings from 4,154 to 4,148, linter/style
warnings from 4,082 to 4,076, and `linter.style.longLine` from 1,898 to
1,892. The isolated Appendix job count changed from 8,703 to 8,701.

## Appendix reconciliation

`HighDimensionalProbability/Appendix.lean` has 15 direct imports.
`APPENDIX_SUMMARY.md` classifies 14 of them as the 14/14 active
source-faithful proved targets; `BorellConvexBody.lean` is the additional
unconditional domain-support import and is not a target completion. The
isolated Appendix closure builds without errors or `sorry` warnings. This is
consistent with the summary, but the build alone does not establish the
summary's semantic classifications; V6, V7, and V10 audit those claims.

## Findings

| ID | Severity | Finding | Evidence |
|---|---|---|---|
| V1-F1 | INFO | The successful clean build logs preserve the complete warning-instance inventory. These diagnostics do not invalidate elaboration, and dependency replay means they are not a unique source-defect count; V8 separately records and adjudicates the unique package-lint rows. | `logs/warning_inventory_recertification.log`; `logs/v1_build_recertification_summary.log`; `logs/recert_v8_package_lint.tsv` |

## Limitations

This verifies a clean rebuild of all project code against cached, hash-pinned dependencies (`.lake/packages` retained; Mathlib oleans from `lake exe cache get`); a from-scratch dependency build was not performed, and dependency integrity rests on the lake-manifest.json pins.

Build success shows well-formedness, not meaning.  A cleanly elaborated
declaration can still be vacuous (V6) or depend on a hollow definition (V7).
The source-state manifest and import-graph audit provide the complementary
snapshot and coverage guarantees.
