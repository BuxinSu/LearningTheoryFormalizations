# V5 — Escape hatches and elaboration trust surface

**Verdict: PASS-WITH-NOTES**

The current 222-file **library-source** scan finds no executable custom
`axiom`, explicit `opaque`, `native_decide`, `unsafe` declaration, compiler
hook, checking-disabling option, elaboration-time environment mutation,
partial definition, or custom macro/elaborator.  All 238 executable library
hits are ordinary options or reviewable non-bypass surfaces, and all are
inventoried.

The compiled exported-instance harness passes, ordinary `autoImplicit`
behavior is measured, the V4 opacity inventory is joined, and the frozen
46-file scratch universe is fully classified.  The verdict is
**PASS-WITH-NOTES** for four INFO-level API/trust-surface facts described
below; none is a kernel bypass.

## Scope

Commands run from the project root
`HighDimensionalProbability/`.  The library scan applies the shared
FILE-WALK rule verbatim:

- every physical `*.lean` below source `HighDimensionalProbability/`,
  excluding `HighDimensionalProbability/Verification/**`;
- every physical `*.lean` below the real project-root
  `MatrixConcentration/` directory;
- no `.lake/**`, Verification deliverable, root import module, or scratch.

This is 212 HDP plus 10 MatrixConcentration files, exactly 222.
`HighDimensionalProbability.lean` is classified separately as the root import
module.  The final separate scratch universe contains all 9 physical
`tmp/*.lean` files and all 37 physical `.audit_work/**/*.lean` files.  Scratch
is never folded into the library count.

The exact library paths/rules are in
[recert_file_universe.txt](logs/recert_file_universe.txt).  Results bind to source-manifest
digest
`78da8753a3367be0ae4c72df049a99f33723a7b22a1d08384714cc59d08853d4`
([manifest check](logs/source_manifest_recertification_check.txt)).

## Scanner and calibration

`lean_source_scanner.py` records raw matches, masks Lean line comments,
nested block comments, and escaped strings without changing offsets, and
marks a hit executable only if it survives masking.  It rejects symlink
inputs, sorts deterministically, and fails on lexical diagnostics.

The V5 profile has 29 detector classes covering:

- `axiom`, explicit `opaque`, `irreducible_def`, `native_decide`, `unsafe`,
  `implemented_by`, `extern`, and `csimp`;
- every `set_option`, with separate checking-disable/bootstrap detectors;
- `run_cmd`, `run_elab`, `#eval`, `initialize`, `modifyEnv`, `addDecl`, and
  `Environment.add`;
- `partial def`, `reducible`, `local instance`, and `Fact`; and
- `macro_rules`, `macro`, `elab_rules`, `elab`, `notation`, `syntax`, and
  `run_tac`.

The fresh calibration evidence is:

- [recert_source_scanner_calibration.log](logs/recert_source_scanner_calibration.log):
  seven passing tests for the current physical universe, offset-preserving
  nested-comment/string masking, non-code negatives, lexical diagnostics,
  and V3/V5 positives;
- [recert_v5_calibration.json](logs/recert_v5_calibration.json), produced by
  the [calibration command](logs/recert_v5_calibration_command.log): every one
  of the 29 detector classes has an executable hit in
  `.audit_work/verification/RecertV3V5ScannerPositive.lean`, including the mandatory
  `native_decide`, `axiom`, `unsafe`, and `run_cmd`.

The [scratch birth audit](logs/recert_v5_scratch_birth_audit.log) records
that all three recertification controls and the instance harness were born
after the pass began.  Older similarly named controls remain untouched and
are not used as current calibration/probe evidence.

Zero library counts therefore do not come from unexercised detectors.

## Exact re-run commands

Run from the project root after the library imports are built:

```text
python3 -B HighDimensionalProbability/Verification/scripts/scan_v5_escape_hatches.py --scope library --format json --output HighDimensionalProbability/Verification/logs/recert_v5_library.json --fail-on-lex-diagnostic
python3 -B HighDimensionalProbability/Verification/scripts/scan_v5_escape_hatches.py --scope library --format tsv --output HighDimensionalProbability/Verification/logs/recert_v5_library.tsv --fail-on-lex-diagnostic
python3 -B HighDimensionalProbability/Verification/scripts/v5_trust_surface.py
~/.elan/bin/lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false .audit_work/verification/RecertV5InstanceAudit.lean
~/.elan/bin/lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false .audit_work/verification/RecertV5AutoImplicitProbe.lean
python3 -B HighDimensionalProbability/Verification/scripts/file_universe.py --paths > HighDimensionalProbability/Verification/logs/recert_file_universe.txt
python3 -B HighDimensionalProbability/Verification/scripts/scan_v5_escape_hatches.py --scope scratch --format json --output HighDimensionalProbability/Verification/logs/recert_v5_scratch.json --fail-on-lex-diagnostic
python3 -B HighDimensionalProbability/Verification/scripts/scan_v5_escape_hatches.py --scope scratch --format tsv --output HighDimensionalProbability/Verification/logs/recert_v5_scratch.tsv --fail-on-lex-diagnostic
python3 -B HighDimensionalProbability/Verification/scripts/v5_scratch_inventory.py --json HighDimensionalProbability/Verification/logs/recert_v5_scratch.json --tsv HighDimensionalProbability/Verification/logs/recert_v5_scratch.tsv --summary HighDimensionalProbability/Verification/logs/recert_v5_scratch_summary.txt --inventory HighDimensionalProbability/Verification/logs/recert_v5_scratch_inventory.tsv
```

`run_logged.py` wrapped each executed command to preserve its exact working
directory, timestamps, elapsed time, output, and exit status in the linked
logs.  The file-universe command's recorded output is
[recert_file_universe.txt](logs/recert_file_universe.txt).

## Commands and evidence

| Check | Exit | Current result | Evidence |
|---|---:|---|---|
| V5 library JSON scan | 0 | 222 files; 293 raw; 238 code; 0 lexical diagnostics | [command](logs/recert_v5_library_json_command.log); [JSON](logs/recert_v5_library.json) |
| V5 library TSV scan | 0 | Independent 293-row serialization | [command](logs/recert_v5_library_tsv_command.log); [TSV](logs/recert_v5_library.tsv) |
| Trust-surface analyzer | 0 | Exact JSON/TSV hit agreement; 0 high-risk code hits; complete option/instance inventories | [command](logs/recert_v5_trust_surface_command.log); [summary](logs/recert_v5_trust_surface_summary.txt) |
| Notation shadow search | 0 | Six source notations and no identical Mathlib declaration | [log](logs/recert_v5_notation_shadow_search.log) |
| Lake auto-implicit configuration search | 0 | `relaxedAutoImplicit=false`; no `autoImplicit` setting | [log](logs/recert_v5_lakefile_autoimplicit_config.log) |
| Compiled instance audit | 0 | All canonicality, proof-irrelevance, fallback-existence, and no-fallback checks compile | [log](logs/recert_v5_instance_audit_build.log); `.audit_work/verification/RecertV5InstanceAudit.lean` |
| Ordinary `autoImplicit` probe | 0 | Prints `{α : Sort u_1} → α → α`; ordinary auto-binding is enabled | [log](logs/recert_v5_auto_implicit_probe.log); `.audit_work/verification/RecertV5AutoImplicitProbe.lean` |
| V4 opacity join | 0 | One internal generated wrapper; 0 project axioms and 0 unexpected user-facing opaques | [V4 summary](logs/recert_axiom_summary.txt); [rows](logs/recert_axiom_and_opaque_declarations.tsv) |
| Final scratch JSON/TSV scan and classifier | 0 | 46 files; exact 238/238 rows; 125 code hits fully classified; 0 `tmp` code hits; 0 lexical diagnostics | [JSON command](logs/recert_v5_scratch_json_command.log); [TSV command](logs/recert_v5_scratch_tsv_command.log); [analysis command](logs/recert_v5_scratch_analysis_command.log); [summary](logs/recert_v5_scratch_summary.txt); [inventory](logs/recert_v5_scratch_inventory.tsv) |

The library JSON and TSV hit multisets agree exactly, not merely in aggregate:
293/293 raw rows and 238/238 executable rows.  Hits occur in 45 files; 39
files have an executable hit.

## Complete 29-pattern library inventory

| Pattern group | Raw | Code | Disposition |
|---|---:|---:|---|
| `axiom` | 2 | 0 | Two explanatory prose uses. |
| `unsafe` | 4 | 0 | Four explanatory docstring uses. |
| `set_option` | 165 | 165 | Resource-limit or linter options only; classified below. |
| `Fact` | 64 | 43 | Explicit typeclass hypotheses/proof-local packaging; classified below. |
| `local instance` | 21 | 21 | Locally scoped structure/probability instances; classified below. |
| `notation` | 34 | 6 | Six parser aliases; classified below. |
| `@[reducible]` | 2 | 2 | Two ordinary transparent bundled definitions. |
| `irreducible_def` | 1 | 1 | One checked implementation definition; classified below. |
| All remaining 21 detector classes | 0 | 0 | No executable or non-code occurrence. |
| **Total** | **293** | **238** | **55 non-code hits; zero lexical diagnostics.** |

The 21 all-zero classes include explicit `opaque`, `native_decide`, every
unsafe/compiler-hook attribute, checking-disable/bootstrap options, every
environment-mutation command, `partial def`, and every macro/elaborator
surface.

## `set_option`: 165 executable hits

Every option row is preserved in
[recert_v5_options.tsv](logs/recert_v5_options.tsv).  The analyzer rejects
unknown option names and nonpositive heartbeat values.

| Option | Count | Trust disposition |
|---|---:|---|
| `maxHeartbeats` | 79 | Positive finite values from 400,000 to 8,000,000; elaboration resource control only. |
| `linter.unusedSectionVars` | 74 | Source-quality linter setting. |
| `linter.unusedFintypeInType` | 6 | Source-quality linter setting. |
| `linter.unusedDecidableInType` | 5 | Source-quality linter setting. |
| `linter.style.setOption` | 1 | Source-quality style-linter setting. |
| **Total** | **165** | **79 resource settings + 86 linter settings.** |

No option disables kernel typechecking or enters bootstrap mode.

## Reviewable non-bypass surfaces

Every executable row in this section, with exact path, line, and context, is
in [recert_v5_reviewable_hits.tsv](logs/recert_v5_reviewable_hits.tsv).

### `Fact`: 43

| File group | Count | Review |
|---|---:|---|
| Chapter 1 consolidated module | 6 | Proof-local witnesses of explicit lower bounds on `ENNReal` exponents. |
| Chapter 3 consolidated module | 2 | One proof-local positive-semidefinite witness and one explicit PSD binder. |
| Chapter 4 consolidated module | 34 | Visible norm-domain binders such as `[Fact (1 ≤ p)]`. |
| MatrixConcentration Chapter 5 | 1 | Proof-local finite-rank equality packaging. |

These are explicit propositions in terms or declaration types; none inserts a
custom axiom or concealed environment declaration.

### `local instance`: 21

The full declaration headers are in
[recert_v5_all_instances.tsv](logs/recert_v5_all_instances.tsv).  Nineteen
occur in six Appendix infrastructure files and install local topology,
measurable/Borel, countability, probability, compact-measure, Haar-invariance,
or permutation structures.  Two Chapter 3 declarations locally install the
proved probability-measure structure for `projectiveProbability`.  Their
`local` scope prevents downstream export, and none manufactures an
unrelated `Fact`.

### Notation: 6

Four `local notation "μˢ"` declarations abbreviate product measures; one
`local notation "gamma"` abbreviates `gaussianReal 0 1`; and the distinctive
`Ent[ f; μ ]` notation abbreviates `entropy μ f`.  There is no `macro`,
`syntax`, or custom elaborator, and the exact-literal Mathlib/source search
finds no standard-token or tactic shadow.

### Reducibility: 2 transparent + 1 irreducible

The two `@[reducible]` declarations are:

- `probabilityHaarIsMulRightInvariant`, packaging a proved Haar-invariance
  result for local installation; and
- `entrywiseL1NormedAddCommGroup`, packaging the entrywise-\(\ell_1\)
  additive-group norm.

Neither is a global instance or proof bypass.  The sole
`irreducible_def` is
`HDP.Chapter8.Appendix.greedyOwnerIndex` at
`Appendix/Infra/MajorizingMeasureRanked.lean:316`.  It supplies an ordinary
checked value and deliberately hides implementation unfolding.  V4 finds
exactly one project-origin `opaque` row: the generated internal hygienic
wrapper for this definition.  The wrapper uses only `propext`,
`Classical.choice`, and `Quot.sound`; V4 finds zero project axiom
declarations and zero unexpected user-facing opaques.

## Exported instances on Mathlib-owned carriers

The source enumerator finds 99 `instance` declarations in total: 77 global,
21 local, and 1 scoped.  Review of all 77 global headers identifies exactly
16 whose carrier is a Mathlib-owned type.  Every row and its evidence name is
in [recert_v5_global_instances.tsv](logs/recert_v5_global_instances.tsv).

| Carrier family | Rows | Overlap classification |
|---|---:|---|
| Real `Matrix m n ℝ` measurable/Borel | 2 | Product `MeasurableSpace.pi`; Borel proof-valued. |
| Complex `Matrix m n ℂ` measurable/Borel | 2 | Product `MeasurableSpace.pi`; Borel proof-valued. |
| Real square `Matrix (Fin n) (Fin n) ℝ` measurable/Borel | 2 | Reuses the shared HDP generic instances. |
| `Equiv.Perm (Fin n)` measurable | 1 | Global value `⊤`; the second in-tree declaration is local and also `⊤`. |
| Orthogonal group compact/measurable/Borel/continuous-inverse | 4 | Measurable/Borel use canonical subtype structures; compact is unique; continuous-inverse has Mathlib's generic `unitary` fallback, equal by proof irrelevance. |
| Special-orthogonal group compact/measurable/Borel/continuous-inverse/topological-group | 5 | Measurable/Borel use canonical subtype structures; the other three are unique exported constructions. |
| **Total** | **16** | **No value-relevant noncanonical overlap.** |

All 16 instances leak into any downstream importer, which is an INFO-level
API fact even when their values are canonical.  The harness
`RecertV5InstanceAudit.lean` names definitional-equality/proof-irrelevance
theorems for every overlapping measurable/Borel row and unregisters the
other project instances to test that no second exported candidate exists.
For orthogonal `ContinuousInv`, unregistering the project declaration
deliberately requires Mathlib's generic `ContinuousInv (unitary R)` fallback
to synthesize; the harness then equates the project proof with that fallback
by proof irrelevance.  The complete harness exits zero.  Its linter-only
unused-variable warnings arise in `True`-valued no-fallback probes and do not
weaken the compiled checks.

## Ordinary `autoImplicit`

The lakefile search proves that `relaxedAutoImplicit = false` is set and that
ordinary `autoImplicit` is not explicitly disabled.  The fresh
`RecertV5AutoImplicitProbe.lean` deliberately uses an undeclared type
parameter `α`.  Its current-tree compile exits zero and prints:

```text
@recertV5AutoImplicitDefaultProbe : {α : Sort u_1} → α → α
```

Thus ordinary auto-binding is enabled even though relaxed implicit-name
matching is disabled.  V6 consumes this measured fact for its
binder-telescope audit.

## Final scratch census

After all audit harnesses were created, the final scan independently
enumerated all physical, non-symlink `tmp/*.lean` and
`.audit_work/**/*.lean` files.  It serialized JSON and TSV, required exact
hit agreement and zero lexical diagnostics, required all 29 detector classes
in the current positive control, rejected executable detector hits in
`tmp`, and allowed only reviewed `set_option`, `run_cmd`, and `partial def`
collector constructs outside planted/historical controls.

| Scratch measurement | Result |
|---|---:|
| files | 46 |
| raw / code / non-code hits | 238 / 125 / 113 |
| JSON/TSV rows | 238 / 238 |
| current positive-control classes / code hits | 29 / 32 |
| current negative-control code hits | 0 |
| historical files / code hits | 21 / 64 |
| current audit harness files / allowed code hits | 14 / 29 |
| executable hits in `tmp` | 0 |
| lexical diagnostics / classification errors | 0 / 0 |

The executable scratch hits are evidence/tooling constructs, not library
declarations: 32 are the deliberately planted current control, 64 are in
enumerated historical controls/harnesses that are not used as current
evidence, and 29 are reviewed collector/resource constructs in current audit
harnesses.

## Findings

| ID | Severity | Finding | Evidence |
|---|---|---|---|
| V5-F1 | INFO | The 222-file library source contains zero executable kernel bypass, custom axiom/opaque command, unsafe/compiler hook, checking-disable option, environment mutation, partial definition, or custom macro/elaborator.  The separate final 46-file scratch surface is exhaustively enumerated and fully classified. | [trust summary](logs/recert_v5_trust_surface_summary.txt); [scratch summary](logs/recert_v5_scratch_summary.txt) |
| V5-F2 | INFO | `greedyOwnerIndex` is the sole source `irreducible_def`; it supplies a checked value rather than an axiom, and V4 confirms its sole generated opaque is internal and uses only the three standard axioms. | [reviewable rows](logs/recert_v5_reviewable_hits.tsv); [V4 opaque row](logs/recert_axiom_and_opaque_declarations.tsv) |
| V5-F3 | INFO | The lakefile disables relaxed implicit-name matching but not ordinary `autoImplicit`; the compiled behavioral probe confirms ordinary auto-binding is enabled. | [configuration log](logs/recert_v5_lakefile_autoimplicit_config.log); [probe log](logs/recert_v5_auto_implicit_probe.log) |
| V5-F4 | INFO | The libraries export 16 instances on Mathlib-owned carriers.  Compiled checks classify them as canonical, proof-irrelevant, or uniquely exported; orthogonal `ContinuousInv` overlaps Mathlib's proof-irrelevant `unitary` fallback.  All 16 affect downstream importers. | [instance rows](logs/recert_v5_global_instances.tsv); [compiled audit](logs/recert_v5_instance_audit_build.log) |

## Limitations

This is a syntactic source audit, calibrated for Lean comments, strings, and
lexical failures.  It does not elaborate macros, inspect compiled dependency
packages, or replace V4's transitive `Lean.collectAxioms` audit.  The current
compiled instance/`autoImplicit` probes and the V4 opacity join cover the
specific build-dependent claims reported above; they do not constitute a
general semantic review of every option, notation, or instance body.

Zero explicit source `opaque` commands does not mean theorem values are
definitionally transparent: Lean theorem opacity and the one generated
`irreducible_def` wrapper are distinct surfaces.  V5 makes no mathematical
faithfulness or non-vacuity claim; those belong to V6/V7/V10.  Trust in the
Lean kernel and pinned Mathlib/Batteries packages is an explicit project
boundary.
