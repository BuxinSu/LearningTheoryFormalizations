# V9 — Published-claims cross-check

**Verdict: PASS-WITH-NOTES**

**Tier: mixed (machine checks plus a light review of record chronology)**

**Finding count: C=0 M=0 m=0 I=1**

## Guarantee

Every machine-checkable self-claim in the source-directory
`MatrixConcentration/README.md` and `APPENDIX_SUMMARY.md` was compared with
the current source snapshot, compiled environment, V1–V5 evidence, or the
separate audit trail. Counts, module coverage, toolchain pins, cleanliness,
endpoint resolution, endpoint axioms, and unresolved-proof closures agree
with measurement. The previously incorrect working-directory instruction was
corrected to name the Lake project root. Deterministic counts below have been
re-measured after the UP-007 / display (6.1.6) correction. The recovery-v7
clean build, fresh aggregate, printed-command checks, warning census, and
standalone V6/V7/V10 reruns all passed. The independent final
lifecycle/report acceptance gate was subsequently run and also passed.

## Method

All commands ran initially from the project root:

```sh
python3 MatrixConcentration/Verification/scripts/source_manifest.py check
python3 MatrixConcentration/Verification/scripts/v6_extract_correspondence.py
/usr/bin/time -p ~/.elan/bin/lake env lean \
  -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false \
  MatrixConcentration/Verification/scripts/v6_endpoint_telescopes.lean \
  > MatrixConcentration/Verification/logs/v6_endpoint_telescopes_compile.log \
  2>&1 &
v9_endpoint_pid=$!
wait "$v9_endpoint_pid"
python3 MatrixConcentration/Verification/scripts/verify_readme_claims.py \
  --production
bash MatrixConcentration/Verification/scripts/calibrate_readme_checker.sh
bash MatrixConcentration/Verification/scripts/test_readme_commands.sh
python3 MatrixConcentration/Verification/scripts/check_translation_records.py
```

`verify_readme_claims.py` extracts rows only from the eight chapter tables
under `## Book → Lean correspondence`. It compares every row position, short
name, published final-module filename, and `thm`/`lem`/`def` role suffix with
the source inventory and the environment dump produced by
`v6_endpoint_telescopes.lean`; that Lean harness resolves the name and calls
`Lean.collectAxioms`. The checker then independently reconciles the resolved
fully qualified name and axiom set with V4's universal
`logs/axiom_audit.tsv`.

The public declaration recount removes Lean comments and strings, recognizes
attributes plus `private`, `protected`, and `noncomputable` modifiers, and
counts non-private source declarations by the exact keywords `theorem`,
`lemma`, and `def`. This is the README's source-level counting rule.
Its source universe is every `.lean` file physically under the project root,
excluding exactly `.lake/**`, `MatrixConcentration/Verification/**`, and
`.audit_work/**`: the 14 flat source modules plus the root module, which
contributes no source declaration.

### Checker calibration

`calibrate_readme_checker.sh` copies the README to
`.audit_work/README_fake_name.md` and appends a row naming
`verificationDefinitelyMissingEndpoint`. The production checker rejected the
copy with exit status 1, reporting 468 rows and that exact unresolved name.
The current README then passed with 467/467 registered rows. Calibration acts
only on the copy and does not modify the current README.

### Final post-correction re-certification

The corrected 20-file source manifest has top-level digest
`38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89`.
The final 147-file verification-input manifest has top-level digest
`119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`.
Endpoint, count, environment, fake-name calibration, printed-command, and
record-chronology checks all passed against those two bound digests.

The formerly accepted recovery-v6 build, its 3,209-job transcript, and its
aggregate/standalone timings remain preserved as historical evidence. They
are explicitly superseded and are not current certification for the corrected
source. Recovery-v7 run `d854807a-23cd-4b3f-81f9-310c36ee9e19` passed from
`2026-07-20T17:08:56Z` through `2026-07-20T17:28:04Z` in 1,148 seconds. Its
previously absent reserved build directory completed 3,209 jobs with all 15
project modules `Built`, none `Replayed`, 1,196 classified warnings, zero
error or missing-proof warning, and build-log SHA-256
`9e25991ff6b5ba971442150cc369ce5d9ef24a2e726f36155435b318116d694f`.
The canonical replay subsequently covered all 15 modules with 0 `Built`, 14
`Replayed`, and exit 0.

Fresh aggregate run `8212cc84-aad8-4abc-b0df-b68fd3241112` passed from
`2026-07-20T17:28:34Z` through `2026-07-20T17:43:35Z` in 901 seconds, with 23
`START`, 23 `PASS`, zero `SKIP`/`FAIL`, terminal
`ALL MACHINE STAGES PASSED`, and log SHA-256
`81b8bb7fa4f415ba1f98e4f5d143390c697bce5e9474ba2464e7a39e303c30b8`.

The source-bound standalone runs then passed in order:

- V6 run `06bd42c9-8921-496e-9029-8abd8ef5c141`,
  `2026-07-20T17:43:57Z`–`2026-07-20T18:25:55Z`, 2,518 seconds, log SHA-256
  `3314e0966da5ee4c972281e5e8f072fcbe5ba5628bea50dc623b3d985daa9f09`;
- V7 run `ea099f89-3c20-466b-bbfb-a4e7abd839f5`,
  `2026-07-20T18:26:10Z`–`2026-07-20T18:30:10Z`, 240 seconds, 51/51 covered as 32
  citation-backed plus 19 witness-backed definitions, 78 dead leaves, log
  SHA-256
  `1d8ab2977e077100389e2283fd79fd1abfb5f1203e8c67c3cd2814b31518b497`;
- standalone-parent V10 run `4501a473-f8a5-49cc-93f7-6b57fe1e3fb3`,
  `2026-07-20T18:30:27Z`–`2026-07-20T18:32:50Z`, 143 seconds, log SHA-256
  `afcfaa944f9336545621fbeb99d9008a16182495f37a9a62aefc8c28b6199adb`.

The original baseline deletion and the earlier re-certification chronology
remain historical evidence. Recovery-v2 completed successfully;
recovery-v3 through recovery-v6 remain preserved only as superseded or
interrupted chronology. The independent final acceptance decision is recorded
in [`logs/final_lifecycle_check.txt`](logs/final_lifecycle_check.txt): it
reports `problems=0`, `result=PASS`, a 14/14 PASS final-claims manifest, and
clear writer-lock/finalization-guard checks; certificate validity requires
both to remain absent.

## Results

### Toolchain, modules, and commands

| Claim | Measurement | Result |
|---|---|---|
| Lean pin | `leanprover/lean4:v4.31.0` in `lean-toolchain` | CONFIRMED |
| Mathlib pin | `inputRev = v4.31.0` in `lake-manifest.json` | CONFIRMED |
| Inner modules | 14 linked, 14 physical, 14 root-imported | CONFIRMED |
| Printed `lake build` command | exit 0 from the documented Lake project root; exit 1 from the former source-directory cwd negative control | CONFIRMED |
| Printed direct-file command | exit 0 from the documented Lake project root; exit 1 from the former source-directory cwd negative control | CONFIRMED |

The source README lives one level below `lakefile.toml`. From its own
directory, the two commands still fail as an intentional negative control:
`lake build` reports that no configuration file exists, while the direct
command addresses a nonexistent nested path. The corrected README explicitly
says “From the Lake project root” and identifies it as the parent directory
containing `lakefile.toml`; both exact printed commands succeed there.

The printed `lake env lean` command is a valid direct elaboration check only
after imports have been built. It does not inherit the lakefile's
`leanOptions`; audit harnesses therefore pass
`-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false` explicitly. The
authoritative library check remains `lake build`.

### Published counts

| Quantity | Published | Measured | Result |
|---|---:|---:|---|
| public `theorem` declarations | 467 | 467 | CONFIRMED |
| public `lemma` declarations | 841 | 841 | CONFIRMED |
| public `def` declarations | 135 | 135 | CONFIRMED |
| public total | 1,443 | 1,443 | CONFIRMED |
| correspondence rows | 467 | 467 | CONFIRMED |
| inner modules | 14 | 14 | CONFIRMED |

The chapter row vector is also exact:
21 / 136 / 35 / 55 / 71 / 62 / 63 / 24.

The 1,443 count is a public source-keyword count. V4's larger 2,213 total is
not a discrepancy: it is an environment-constant census that intentionally
includes mangled private declarations and compiler-generated constants. The
fresh V8 inventory splits the environment total into 1,449 named and 764
generated declarations. Package lint reports zero hits across 16 linters; the
1,196 recovery-v7 build warnings are classified as 813 MINOR maintenance rows
and 383 INFO style rows.

### Correspondence-table resolution and axioms

All 467 mechanically checkable endpoint cells agree:

| Row claim | Measured agreement |
|---|---:|
| declaration short name | 467 / 467 |
| final-module filename | 467 / 467 |
| source role suffix | 467 / 467 |

The role suffix recount is 297 `thm`, 104 `lem`, and 66 `def`; the first two
resolve as theorem/proof constants and the last as definitions:

| Environment kind | Rows | Exact axiom set |
|---|---:|---|
| theorem/proof constant | 401 | 401 / 401 |
| definition | 66 | 66 / 66 |
| **Total** | **467** | **467 / 467** |

For every row, both the dedicated collector and V4 record exactly
`Classical.choice`, `Quot.sound`, and `propext`. In particular, the 401
theorem/lemma endpoints confirm the README's exact-three-axiom endpoint
claim; the check additionally establishes the same exact set for the 66
definition rows.

The `E`/`I`/`M`/`S`/`V` role prefix, book-source description, and prose notes
encode source correspondence and audit status rather than a source-declaration
fact. Their book-faithfulness remains outside this pass.

### V6 and V7 scope reconciliation

The corrected V6 ledger covers exactly the same 467 registered endpoints:
433 are classified OK, 34 are classified SUSPECT with accepted
endpoint-dependent evidence, and none is classified VACUOUS. Tier C covers
all 74 obligations: 40 sampled OK rows plus all 34 SUSPECT rows, with 20
`NAMED_APPLICATION` and 54 `LIBRARY_CITATION` dispositions.

The fresh V7 run resolved 1,443 public and 82 private declarations, 1,525 in
all, and enumerated all 149 definition candidates. Its load-bearing register
is covered 51/51, split into 32 citation-backed and 19 witness-backed rows.
The post-terminal dead-code census contains 78 declarations: 76 public and
two private (43 theorems, 32 lemmas, and three definitions).

### Cleanliness claim

The published claim is **CONFIRMED**:

| Subclaim | Measurement |
|---|---|
| no `sorry` or `admit` | V3 scanned all 15 physical files; zero textual hits and zero `sorryAx` dependencies |
| no `native_decide` | V5 full-universe scan: zero |
| no custom axioms | V4 audited all 2,213 loaded declarations; zero exceedances and zero declared project axioms |
| exact standard axioms at audited endpoints | 467 / 467 correspondence rows, including all 401 theorem/lemma rows |
| isolated clean root build | Recovery-v7: previously absent reserved directory, 3,209 jobs, 15 `Built`, 0 `Replayed`, 1,196 warnings, zero error or missing-proof warning, exit 0 |
| canonical root replay | Recovery-v7-bound replay: all 15 modules covered, 0 `Built`, 14 `Replayed`, 1,196 warnings, zero error or missing-proof warning, exit 0 |

V4 proves the stronger universal “no axiom beyond the standard three” result
for every loaded project declaration, not only the published endpoints.

### Appendix and unresolved-proof ledgers

`APPENDIX_SUMMARY.md` §6 agrees with the compiled environment:

| Item | Proved declaration evidence | Result |
|---|---|---|
| UP-001 | `matrix_bernstein_tail` | CONFIRMED |
| UP-002 | `matrix_bernstein_expectation` | CONFIRMED |
| UP-003 | `lieb_trace_exp_log_concave` | CONFIRMED |
| UP-004 | `golden_thompson_trace` | CONFIRMED |
| UP-005 | `gauss_concentration` | CONFIRMED |
| UP-006 | `matrix_rosenthal` | CONFIRMED |
| UP-007 | no registered Lean counterpart for the literal book display (6.1.6) | FORMAL-COVERAGE EXCEPTION |
| UP-008 | `symmetric_sum_lower_bound` | CONFIRMED |

The seven registered coverage items resolve with exactly the standard three
axioms. All five appendix modules are root-imported, built by recovery-v7,
clean under V3/V5, and universally covered by V4. UP-007 / (6.1.6) is the sole
declared formal-coverage exception:
no registered Lean counterpart is asserted. The retained bounded
`matrix_rosenthal_pinelis_symmetric` and
`matrix_rosenthal_pinelis_centered_with_loss` results and their `_aux`
helpers remain useful support declarations, but are explicitly
non-correspondence infrastructure.

### Separate TranslationReport trail

The light chronology-aware check enumerated 63 Markdown records and found
COMPLETE status in all seven chapter checkpoint files. Chapter 6 records the
UP-001/002 discharges; Chapter 8 records the later UP-003 discharge; the final
publication audit states zero open blockers. Fourteen `open` rows remain in
earlier snapshots—four in the Chapter 6 build report, six in the Chapter 7
build report, and four in the Appendix report—but these are historical states
superseded by the later records and current `APPENDIX_SUMMARY.md`, as the
project's live-ledger chronology specifies. No current README-to-record status
mismatch was found.

The project-root README contains only stale repository-template
instructions and no mathematical claim; V2 records it as V2-F3.

## Findings

### V9-F1 — INFO — FIXED: README now names the Lake project root

The pre-correction instruction was independently confirmed to name the wrong
working directory. The minimal one-line documentation correction now
explicitly names the parent Lake project root containing `lakefile.toml`.
The command harness records project-root exit statuses 0/0 and former
source-directory negative-control statuses 1/1, with measured result
`PRINTED_PROJECT_ROOT_COMMANDS_SUCCEED_SOURCE_CWD_NEGATIVE_CONTROL_FAILS`.
No Lean declaration, API, or proof was changed by this documentation fix.

## Raw evidence

- [`logs/v9_readme_claims_summary.txt`](logs/v9_readme_claims_summary.txt) —
  validated claim totals and zero checker problems.
- [`logs/v9_readme_endpoints.tsv`](logs/v9_readme_endpoints.tsv) — all 467
  extracted names, published/measured modules, published/measured source-role
  kinds, resolutions, environment kinds, two axiom measurements, and results.
- [`logs/v9_public_source_counts.tsv`](logs/v9_public_source_counts.tsv) —
  source-keyword recount.
- [`logs/v9_readme_calibration_summary.txt`](logs/v9_readme_calibration_summary.txt)
  and [`logs/v9_readme_calibration_check.log`](logs/v9_readme_calibration_check.log)
  — calibrated fake-name rejection.
- [`logs/v9_readme_commands_summary.txt`](logs/v9_readme_commands_summary.txt)
  — four cwd/command exit statuses.
- [`logs/v9_readme_source_build.log`](logs/v9_readme_source_build.log),
  [`logs/v9_readme_source_direct.log`](logs/v9_readme_source_direct.log),
  [`logs/v9_readme_root_build.log`](logs/v9_readme_root_build.log), and
  [`logs/v9_readme_root_direct.log`](logs/v9_readme_root_direct.log) — exact
  command outputs.
- [`logs/v9_ledger_endpoints.tsv`](logs/v9_ledger_endpoints.tsv) — UP-001
  through UP-008 compiled mappings.
- [`logs/v9_translation_consistency.txt`](logs/v9_translation_consistency.txt)
  — chronology-aware light record check.
- [`logs/source_manifest.txt`](logs/source_manifest.txt) — the exact 20-input
  source and claims snapshot certified by this rerun.
- [`logs/verification_input_manifest_summary.txt`](logs/verification_input_manifest_summary.txt)
  — the 147-file verification-input inventory and its bound digest.
- [`logs/build_full.recertification-empty-recovery.log`](logs/build_full.recertification-empty-recovery.log)
  and its status record — the accepted recovery-v7 isolated empty-build
  transcript and PASS status; preserved recovery-v6 evidence is historical.
- [`logs/v1_canonical_build_before.tsv`](logs/v1_canonical_build_before.tsv)
  and [`logs/v1_canonical_build_after.tsv`](logs/v1_canonical_build_after.tsv)
  — matching inventories proving that the isolated build did not change the
  canonical build tree.
- [`logs/v10_summary.txt`](logs/v10_summary.txt) — the exact
  environment/V4 coverage guard, 14-predicate classification, manual-review
  totals, calibration totals, and production census verdict.
- [`curation/v10_inline_adjudication.tsv`](curation/v10_inline_adjudication.tsv)
  and [`logs/v10_inline_review_queue.tsv`](logs/v10_inline_review_queue.tsv) —
  all 368 residual type-hash adjudications and the empty final queue.
- [`logs/v10_disclosure_reconciliation.tsv`](logs/v10_disclosure_reconciliation.tsv)
  — publication/disclosure reconciliation for the conditional interfaces.
- [`logs/v10_run.aggregate.log`](logs/v10_run.aggregate.log) and
  [`logs/v10_run_status.aggregate.log`](logs/v10_run_status.aggregate.log) —
  the aggregate's frozen V10 child transcript and status.
- [`logs/v10_run.log`](logs/v10_run.log) and
  [`logs/v10_run_status.log`](logs/v10_run_status.log) — the later final
  standalone V10 transcript and status.
- [`logs/run_all.log`](logs/run_all.log),
  [`logs/run_all_status.log`](logs/run_all_status.log), and the standalone
  V6/V7/V10 logs and status files — the authoritative aggregate and ordered
  current source-bound chronology. Preserved supervisor files refer to the
  superseded recovery-v6 chain.
- [`logs/final_lifecycle_check.txt`](logs/final_lifecycle_check.txt) — the
  independent terminal lifecycle/report acceptance gate: PASS with zero
  problems, 14/14 final claims, and absent writer lock/finalization guard;
  certificate validity requires both to remain absent.

## Limitations

Book-faithfulness is explicitly out of scope. This report checks consistency
of the library's self-claims and only the status chronology of the separate
TranslationReport trail; it does not repeat that trail's source comparison.

Endpoint resolution and axiom collection trust the Lean kernel and the pinned
Mathlib environment. The direct-file command test uses already-built imports,
as documented. Human prose with no machine-checkable project-status content
was not treated as a separate claim.

V3's placeholder scan and V4's axiom audit cannot by themselves establish
that every proposition-valued hypothesis is discharged somewhere in source;
that broader coverage expansion is outside V9's claims cross-check.

The recovery-v7 build, final aggregate `run_all.sh --fresh`, standalone
V6/V7/V10 re-certification, and independent lifecycle/report acceptance are
complete. The linked `logs/final_lifecycle_check.txt` records the terminal
PASS. The PASS statements above remain limited to the described mechanical
claims cross-check; book-faithfulness remains outside V9.
