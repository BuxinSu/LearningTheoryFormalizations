# V8 — Linter and code-quality pass

**Verdict: PASS-WITH-NOTES**

The current restructured tree passes the complete package-scope coverage
gate.  The existing V8 harness imports the HDP root, the isolated Appendix
closure, and all ten real MatrixConcentration modules before running
`#lint in HighDimensionalProbability` and
`#lint in MatrixConcentration`.

The run examined 7,650 HDP declarations and 1,012 MatrixConcentration
declarations with 16 Batteries linters per package.  It reported 68
declaration-level quality hits; the parser recovered exactly the same 68
unique rows, found no non-lint Lean error, and classified the full
222-file physical surface as `COMPLETE`.  The currently linked V1 build
evidence separately contributes its complete warning-instance inventory.
These are maintenance signals, not mechanical-soundness failures.

Relative to the pre-removal baseline, the physical surface changed from 224
to 222 files, the linter examined-declaration count from 8,677 to 8,662, the
generated-declaration count from 6,375 to 6,360, and the unique hit count from
166 to 68.  Round 10 repaired all 97 previously reported missing declaration
docstrings without changing any declaration, signature, or proof body.

This report has 0 CRITICAL, 0 MAJOR, 0 MINOR, and 3 INFO findings.  Under
R6, INFO findings with complete coverage require
`PASS-WITH-NOTES`.

## Quality-only interpretation

V8 audits documentation, naming, API shape, simplifier normal form, unused
arguments, and other maintainability surfaces.  A linter hit is MINOR or
INFO by itself; it does not show that a theorem is false, vacuous, unproved,
or axiom-unsafe.  Those questions belong to V3–V7 and V10.

Conversely, package-lint success cannot establish mathematical correctness
or book faithfulness.  V8's guarantee is narrower: both package-scoped
commands ran over the complete current project surface, every emitted hit
was captured, and no quality warning is being presented as a kernel defect.

## Scope and coverage

The shared FILE-WALK UNIVERSE is:

- every physical `*.lean` below `HighDimensionalProbability/`, excluding
  `HighDimensionalProbability/Verification/**`;
- every physical `*.lean` below the real project-root
  `MatrixConcentration/` directory;
- no `.lake/**`, Verification deliverable, root import module, or scratch.

This is 212 HDP files plus 10 MatrixConcentration files, exactly 222.
`HighDimensionalProbability.lean` is the separate HDP root, making 223
environment modules.  There is no MatrixConcentration root module; the
lakefile selects all ten modules with the `MatrixConcentration.+` glob.

V2 proves that the exclusive 222-file partition is 111 HDP-root-reachable
files plus 111 Appendix-only files, with zero orphan, unresolved import, or
cycle.  All ten MatrixConcentration files are glob-built and also reachable
from the HDP root.  V1 proves that the complete root/MatrixConcentration and
isolated Appendix targets build successfully.

The V8 harness `.audit_work/verification/V8PackageLintRecertification.lean`
is a physical pre-existing local audit file. No new scratch Lean file was
created.  It explicitly imports:

```text
HighDimensionalProbability
HighDimensionalProbability.Appendix
MatrixConcentration.Prelude
MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices
MatrixConcentration.Chapter3_MatrixLaplaceTransformMethod
MatrixConcentration.Chapter4_MatrixGaussianAndRademacherSeries
MatrixConcentration.Chapter5_SumOfPSDMatrices
MatrixConcentration.Chapter8_ProofOfLiebsTheorem
MatrixConcentration.Appendix_GoldenThompson
MatrixConcentration.Appendix_GaussianConcentration
MatrixConcentration.Appendix_SymmetricLowerBound
MatrixConcentration.Appendix_MatrixRosenthal
```

It then contains exactly these commands, in this order:

```lean
#lint in HighDimensionalProbability
#lint in MatrixConcentration
```

A bare `#lint` in an import-only file can lint only the harness and produce a
false near-zero all-clear.  The V8 parser therefore requires exactly one
summary for each named package, in command order, and rejects a package
summary with fewer than 1,000 declarations.

All results apply to source-manifest digest
`78da8753a3367be0ae4c72df049a99f33723a7b22a1d08384714cc59d08853d4`.
The file universe and zero-orphan evidence are
[recert_file_universe.txt](logs/recert_file_universe.txt),
[recert_import_graph.txt](logs/recert_import_graph.txt), and
[v2_orphan_recertification_summary.log](logs/v2_orphan_recertification_summary.log).

## Runner, parser, and calibration

[run_v8_package_lint.py](scripts/run_v8_package_lint.py) validates the
harness before invoking Lean.  It:

- requires the exact ordered import and package-command lists above;
- masks comments and strings before reading the harness;
- requires the current V2 zero-orphan evidence;
- refuses a live run without `--confirm-v7-complete`;
- invokes `lake env lean` with unlimited lint heartbeats, Batteries lint
  tracing, and `warningAsError=false`; and
- normalizes raw Lean exit 1 as expected only when nonzero lint summaries
  and parsed rows reconcile.

[v8_lint_parser.py](scripts/v8_lint_parser.py) independently checks:

- exactly one command header and one exit footer;
- all three required `-D` flags;
- the full-surface harness identity;
- exactly one summary for each package, in order;
- at least 1,000 examined declarations per package;
- reported-error count equal to parsed top-level `#check` rows;
- every hit grouped under the correct package prefix;
- no non-lint Lean error header; and
- raw exit 1 iff lint hits exist, or raw exit 0 iff none exist.

The parser understands nested Lean block comments in formatted linter
output, so module-looking and `#check`-looking diagnostic text cannot become
false rows.  It emits complete JSON, text, and 68-row TSV inventories.

The planted parser fixture is not live-project evidence.  The fresh
[recert_v8_tests.log](logs/recert_v8_tests.log) records all 14 tests passing,
including exact harness imports, both package commands, required flags,
full-surface status, the thousand-declaration gate, malformed-summary and
non-lint-error rejection, expected nonzero semantics, nested-comment decoy
rejection, and one TSV row per hit.

## Exact re-run commands

Run from the project root after V7 is final and V1 has built the imports:

```text
python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py --log HighDimensionalProbability/Verification/logs/recert_v8_tests.log -- python3 -B HighDimensionalProbability/Verification/scripts/test_v8_package_lint.py

python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py --log HighDimensionalProbability/Verification/logs/recert_v8_dry_run_command.log -- python3 -B HighDimensionalProbability/Verification/scripts/run_v8_package_lint.py --dry-run

python3 -B HighDimensionalProbability/Verification/scripts/run_v8_package_lint.py --dry-run > HighDimensionalProbability/Verification/logs/recert_v8_dry_run.log

python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py --log HighDimensionalProbability/Verification/logs/recert_v8_package_lint_driver.log -- python3 -B HighDimensionalProbability/Verification/scripts/run_v8_package_lint.py --confirm-v7-complete

python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py --log HighDimensionalProbability/Verification/logs/recert_v8_package_lint_summary_command.log -- python3 -B HighDimensionalProbability/Verification/scripts/v8_lint_parser.py HighDimensionalProbability/Verification/logs/recert_v8_package_lint.log --format text --output HighDimensionalProbability/Verification/logs/recert_v8_package_lint_summary.txt

python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py --log HighDimensionalProbability/Verification/logs/recert_v8_package_lint_tsv_command.log -- python3 -B HighDimensionalProbability/Verification/scripts/v8_lint_parser.py HighDimensionalProbability/Verification/logs/recert_v8_package_lint.log --format tsv --output HighDimensionalProbability/Verification/logs/recert_v8_package_lint.tsv
```

The runner's inner preserved command is:

```text
lake env lean -DmaxHeartbeats=0 -Dtrace.Batteries.Lint=true -DwarningAsError=false .audit_work/verification/V8PackageLintRecertification.lean
```

The current V1 warning inventory is reproduced by:

```text
python3 -B HighDimensionalProbability/Verification/scripts/warning_inventory.py HighDimensionalProbability/Verification/logs/build_full_recertification.log HighDimensionalProbability/Verification/logs/build_appendix_recertification.log > HighDimensionalProbability/Verification/logs/warning_inventory_recertification.log
```

## Command results

| Check | Exit | Result | Evidence |
|---|---:|---|---|
| 14-test V8 calibration | 0 | all tests pass | [test log](logs/recert_v8_tests.log) |
| exact dry-run preview | 0 | expected full-surface Lean command | [command log](logs/recert_v8_dry_run_command.log); [preview](logs/recert_v8_dry_run.log) |
| raw package-scope Lean run | 1 | expected because 68 lint messages were emitted; no non-lint error | [raw log](logs/recert_v8_package_lint.log) |
| logged V8 driver | 0 | 68 reported = 68 parsed; full coverage `PASS` | [driver log](logs/recert_v8_package_lint_driver.log); [JSON](logs/recert_v8_package_lint.json) |
| independent text serialization | 0 | gate passed; no diagnostics | [command](logs/recert_v8_package_lint_summary_command.log); [summary](logs/recert_v8_package_lint_summary.txt) |
| independent TSV serialization | 0 | header + 68 unique data rows | [command](logs/recert_v8_package_lint_tsv_command.log); [TSV](logs/recert_v8_package_lint.tsv) |
| V1 warning classifier | 0 | 4,376/4,376 warning headers parsed in the currently linked build evidence | [inventory](logs/warning_inventory_recertification.log); [V1 summary](logs/v1_build_recertification_summary.log) |

The raw Lean process took 93.086 seconds.  Its exit 1 is the normal
`#lint` result for a nonempty finding set.  The outer driver took 93.217
seconds and exited 0 only after the parser established:

```text
surface_profile: full-physical-surface
coverage_status: COMPLETE
coverage_complete: true
gate_passed: true
overall_status: PASS
diagnostics: none
```

## Package-scope result

| Package | Declarations examined | Automatically generated | Linters | Reported | Parsed |
|---|---:|---:|---:|---:|---:|
| `HighDimensionalProbability` | 7,650 | 5,864 | 16 | 65 | 65 |
| `MatrixConcentration` | 1,012 | 496 | 16 | 3 | 3 |
| **Total** | **8,662** | **6,360** | **16 per package** | **68** | **68** |

The 68 declaration names are unique.  Five linters have nonzero results;
the other eleven executed successfully with zero hits.

| Linter | HDP | MatrixConcentration | Total | Disposition |
|---|---:|---:|---:|---|
| `checkUnivs` | 0 | 0 | 0 | clean |
| `defLemma` | 4 | 0 | 4 | INFO: changing declaration transparency/form would be an API decision |
| `defsWithUnderscore` | 2 | 0 | 2 | INFO: established public naming convention |
| `deprecatedNoSince` | 0 | 0 | 0 | clean |
| `docBlame` | 0 | 0 | 0 | clean; all 97 Round-9 rows were repaired in Round 10 |
| `dupNamespace` | 0 | 0 | 0 | clean |
| `impossibleInstance` | 0 | 0 | 0 | clean |
| `nonClassInstance` | 0 | 0 | 0 | clean |
| `simpComm` | 1 | 0 | 1 | INFO: existing simplifier-orientation advisory |
| `simpNF` | 13 | 0 | 13 | INFO: existing simplifier-normal-form advisories |
| `simpVarHead` | 0 | 0 | 0 | clean |
| `structureInType` | 0 | 0 | 0 | clean |
| `synTaut` | 0 | 0 | 0 | clean |
| `tacticDocs` | 0 | 0 | 0 | clean |
| `unusedArguments` | 45 | 3 | 48 | INFO: stable API/typeclass arguments unused by the current body |
| `unusedHavesSuffices` | 0 | 0 | 0 | clean |
| **Total** | **65** | **3** | **68** | **all nonzero rows classified INFO** |

No hit is an impossible instance, a non-class instance, a universe-check
failure, a duplicate namespace, or a non-lint elaboration error.  The
former `structureInType` row for the removed
`HDP.Chapter8.GaussianChevetUpperPrinciple` is gone, leaving that linter clean.
The 97 former `docBlame` rows are absent.  Their one-line declaration
docstrings and the absence of any substantive source delta are independently
certified by [the Round-10 delta log](logs/round10_docstring_delta.log).
Likewise, `unusedArguments` means a declaration has parameters the body does
not need; it does not make a theorem's hypotheses inconsistent.

### Complete nonzero module inventory

Every declaration row is in
[recert_v8_package_lint.tsv](logs/recert_v8_package_lint.tsv).  The following
table accounts for all 68 rows by package and module; every project module
not listed has zero package-lint hits.

| Package | Module | Hits |
|---|---|---:|
| HDP | `HighDimensionalProbability.Appendix.BrownianReflection` | 1 |
| HDP | `HighDimensionalProbability.Appendix.Infra.HaarEntropy` | 1 |
| HDP | `HighDimensionalProbability.Appendix.Infra.PoincareCap` | 1 |
| HDP | `HighDimensionalProbability.Appendix.Infra.PoincareQuantile` | 1 |
| HDP | `HighDimensionalProbability.Appendix.Infra.SLT.GaussianLSI.BernoulliLSI` | 1 |
| HDP | `HighDimensionalProbability.Appendix.Infra.SLT.GaussianLSI.DualityEntropy` | 1 |
| HDP | `HighDimensionalProbability.Appendix.Infra.SLT.GaussianPoincare.Limit` | 2 |
| HDP | `HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalFiberSmoothCore` | 1 |
| HDP | `HighDimensionalProbability.Appendix.Infra.SphericalMoment` | 1 |
| HDP | `HighDimensionalProbability.Appendix.Infra.SphericalSymmetrization` | 1 |
| HDP | `HighDimensionalProbability.Appendix.Infra.SymmetricGroupCode` | 1 |
| HDP | `HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions` | 10 |
| HDP | `HighDimensionalProbability.Chapter4_RandomMatrices` | 5 |
| HDP | `HighDimensionalProbability.Chapter5_ConcentrationWithoutIndependence` | 3 |
| HDP | `HighDimensionalProbability.Chapter6_QuadraticFormsSymmetrizationContraction` | 4 |
| HDP | `HighDimensionalProbability.Chapter7_RandomProcesses` | 1 |
| HDP | `HighDimensionalProbability.Exercise.Chapter8.Sec01` | 4 |
| HDP | `HighDimensionalProbability.Exercise.Chapter8.Sec03` | 1 |
| HDP | `HighDimensionalProbability.Exercise.Chapter8.Sec05` | 2 |
| HDP | `HighDimensionalProbability.Chapter8_Chaining` | 5 |
| HDP | `HighDimensionalProbability.Chapter9_DeviationsOfRandomMatricesOnSets` | 3 |
| HDP | `HighDimensionalProbability.Prelude.GaussianMatrix` | 2 |
| HDP | `HighDimensionalProbability.Prelude.MetricEntropy` | 5 |
| HDP | `HighDimensionalProbability.Prelude.RandomGraph` | 1 |
| HDP | `HighDimensionalProbability.Prelude.RandomMatrix` | 4 |
| HDP | `HighDimensionalProbability.Prelude.Sphere` | 2 |
| HDP | `HighDimensionalProbability.Prelude.StochasticBlockModel` | 1 |
| MatrixConcentration | `MatrixConcentration.Chapter3_MatrixLaplaceTransformMethod` | 1 |
| MatrixConcentration | `MatrixConcentration.Chapter5_SumOfPSDMatrices` | 1 |
| MatrixConcentration | `MatrixConcentration.Chapter8_ProofOfLiebsTheorem` | 1 |
| **Total** | **30 modules with nonzero hits** | **68** |

## V1 build-warning fold-in

V1's current warning inventory parses both successful clean-state build
logs with the lakefile linter options active.

| Build log | All warning instances | `sorry` | Other |
|---|---:|---:|---:|
| `build_full_recertification.log` | 1,915 | 228 | 1,687 |
| `build_appendix_recertification.log` | 2,461 | 0 | 2,461 |
| **Total** | **4,376** | **228** | **4,148** |

The 228 `sorry` warnings are the exact ledgered Exercise set reconciled by
V3/V4; they are not a V8 quality finding.  The remaining 4,148 instances
are 72 deprecations and 4,076 linter/style diagnostics:

| Warning class | Instances |
|---|---:|
| `deprecation` | 72 |
| `linter.flexible` | 32 |
| `linter.overlappingInstances` | 2 |
| `linter.style.cdot` | 2 |
| `linter.style.docString` | 2 |
| `linter.style.emptyLine` | 285 |
| `linter.style.header` | 1 |
| `linter.style.longLine` | 1,892 |
| `linter.style.maxHeartbeats` | 18 |
| `linter.style.multiGoal` | 46 |
| `linter.style.openClassical` | 1 |
| `linter.style.setOption` | 86 |
| `linter.style.show` | 383 |
| `linter.style.whitespace` | 32 |
| `linter.unnecessarySeqFocus` | 26 |
| `linter.unnecessarySimpa` | 26 |
| `linter.unreachableTactic` | 2 |
| `linter.unusedDecidableInType` | 748 |
| `linter.unusedFintypeInType` | 334 |
| `linter.unusedSectionVars` | 19 |
| `linter.unusedSimpArgs` | 86 |
| `linter.unusedTactic` | 9 |
| `linter.unusedVariables` | 44 |
| **Non-`sorry` total** | **4,148** |

These are warning-header instances, not distinct source defects.  The root
and Appendix builds overlap heavily, and Lake can replay dependency
warnings.  The report therefore does not invent a deduplicated count.
Build warnings and package-scope lint hits use different frontends and
scopes, so 4,148 and 68 are not added together.  These V1 figures are the
final current V1 build evidence; V8 does not substitute its package-lint run
for that build replay.

## Findings

| ID | Severity | Finding | Evidence |
|---|---|---|---|
| V8-F1 | INFO | The full package-scope run reports 68 declaration-level API, naming, and automation advisories: 48 unused-argument, 13 simp-normal-form, 4 def/lemma-form, 2 naming, and 1 simp-commutativity row. Exact row adjudication found no mathematical, proof-closure, documentation, or coverage defect; changing these rows would alter stable signatures, names, declaration transparency, or simplifier behavior, including three vendored MatrixConcentration rows. | [row inventory](logs/recert_v8_package_lint.tsv); [JSON](logs/recert_v8_package_lint.json); [raw output](logs/recert_v8_package_lint.log) |
| V8-F2 | INFO | The successful V1 build logs' non-`sorry` warnings are a replayed warning-instance view, not a unique source-defect count. Their exact current classification is preserved in the V1 inventory; the actionable declaration-level documentation set was the 97-row `docBlame` population fixed in Round 10. | [warning inventory](logs/warning_inventory_recertification.log); [V1 summary](logs/v1_build_recertification_summary.log); [Round-10 delta](logs/round10_docstring_delta.log) |
| V8-F3 | INFO | Package scope and physical-file coverage are complete: both package commands ran, 8,662 declarations and 6,360 generated declarations were recorded, 68/68 hits reconciled across 30 modules, all 222 source files are on covered build surfaces, the environment has 223 modules, and no module is excluded. | [summary](logs/recert_v8_package_lint_summary.txt); [driver](logs/recert_v8_package_lint_driver.log); [V2 evidence](logs/v2_orphan_recertification_summary.log) |

## Limitations

- Batteries `#lint` runs the 16 linters listed above, not every conceivable
  semantic or style analysis.
- Package declaration counts use the linter frontend's generated-declaration
  filtering and therefore need not equal V4's exhaustive environment
  constant count.
- Raw Lean exit 1 is expected for nonzero linter results.  The driver can
  distinguish it from elaboration/import failure only because both package
  summaries, all row counts, and non-lint error headers are checked.
- V1 warning totals are log instances; overlapping build closures and
  dependency replay prevent treating them as unique source issues.
- `lake env lean` does not inherit every lakefile linter option.  V8 supplies
  the three runtime flags required for package linting explicitly, while the
  complementary V1 builds record the lakefile warning profile.
- V8 does not lint Mathlib or Batteries as project packages.  Their pinned
  revisions and the Lean kernel remain outside this project's quality
  review.
- Round 10 changed only declaration documentation. The remaining 68 rows
  are retained INFO-level API and automation advisories; V8 does not infer
  that changing a public signature, name, transparency mode, or simp set
  would be behavior-preserving.
