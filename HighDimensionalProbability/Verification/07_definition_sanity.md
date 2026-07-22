# V7 — Definition sanity and dead-code reachability

**Verdict: PASS-WITH-NOTES**

The current 223-module environment was exhaustively inventoried. Its 15,022
project declarations have 1,448,224 unique direct type/value dependency
edges, and the environment module set exactly equals the independently
expected current surface. The load-bearing rule selects 270 definitions,
structures, and classes. Every row has a final review disposition: 228 are
`VERIFIED_CITATION`, 42 are `VERIFIED_WITNESS`, none is
`UNVERIFIED_SANITY`, and none is `UNREVIEWED`.

The final residual-closure pass supplies nine clean compiled theorems for the
10 formerly unverified rows. Each theorem retains the exact audited
definition as a direct kernel-type dependency; together they exercise
positive, nonconstant, contrasting-failure, or intended boundary behavior.

This report has 0 CRITICAL, 0 MAJOR, 0 MINOR, and 3 INFO findings.

## Claim and scope

V7 asks whether definitions used by the library have demonstrated
nondegenerate behavior: they should not accidentally be constant, identically
zero, reduced to an empty-index default, or forced to an unintended
measure/typeclass interpretation.

The file-walk universe is every physical `.lean` file under
`HighDimensionalProbability/` union every physical `.lean` file under the real
project-root `MatrixConcentration/` directory. It excludes
`HighDimensionalProbability/Verification/**` and `.lake/**`.
`HighDimensionalProbability.lean` is treated separately as the environment
root. Files in `tmp/*.lean` and `.audit_work/**/*.lean` are separately
classified scratch and are not library files.

The complete environment consists of 222 physical library modules plus the
HDP root, for 223 modules. It includes the HDP root closure, the isolated
Appendix closure, and all 10 glob-built `MatrixConcentration` modules. There
is no `MatrixConcentration` root module. Book-faithfulness is outside V7.

## Machine inventory

The frozen local Lean harness
`.audit_work/verification/DefinitionSanityRecertification.lean` imports the
complete surface explicitly. It records:

- every project constant and its kind, module, privacy, and internal status;
- every direct constant dependency from both declaration types and values;
- every imported project module, including import-only aggregators; and
- an unreferenced and a referenced private calibration definition.

The analyzer
[definition_sanity.py](scripts/definition_sanity.py) independently derives the
expected module set from the current physical layout, checks it against the
environment, joins the constants to fresh V4 and V6 evidence, applies the
load-bearing rule, and classifies zero-reverse declarations.

| Integrity measurement | Result |
|---|---:|
| Expected / environment modules | 223 / 223 |
| Missing / extra modules | 0 / 0 |
| Modules represented by constant rows | 193 |
| Import-only modules with no constant rows | 30 |
| Project constants | 15,022 |
| Unique direct type/value dependency edges | 1,448,224 |
| Unknown edge sources | 0 |
| Inconsistent source metadata | 0 |
| Inconsistent project-target metadata | 0 |
| Constants outside the environment module set | 0 |
| Exact V4 environment-name-set match | yes |
| Analyzer hard failures | none |
| Dead-code calibration | PASS |

The raw harness completed with exit 0 in 1,486.901 seconds. Its principal
artifacts are the [module list](logs/recert_definition_modules.txt),
[constant inventory](logs/recert_definition_constants.tsv),
[dependency edges](logs/recert_definition_dependency_edges.tsv), and
[calibration rows](logs/recert_definition_dead_code_calibration.tsv). The
completed raw collector command, heartbeats, elapsed time, and terminal exit
are in the [collector build log](logs/recert_definition_sanity_build.log).

The analyzer's initial exit 2 is intentional: its machine output remains
`INCOMPLETE` until a separate fail-closed semantic register disposes every
load-bearing row. It reported no hard failure, and the completed register
below closes that coverage gate with no residual negative disposition. See
the [analyzer command log](logs/recert_v7_definition_analyze_command.log),
[machine summary](logs/recert_definition_sanity_summary.txt), and
[module coverage ledger](logs/recert_definition_module_coverage.txt).

## Load-bearing rule

The load-bearing union follows the required fixed rule:

1. every definition, structure, and class in `Prelude/`; and
2. every definition directly referenced by at least three distinct V6
   Tier-B theorem endpoints.

Compiler-generated recursors and structure helpers are not source definitions
about which theorems reason. The analyzer therefore records and excludes 27
such generated Prelude helpers from the blanket Prelude input rather than
turning them into false semantic obligations.

| Input or result | Rows |
|---|---:|
| Fresh V6 Tier-B theorem endpoints | 519 |
| Prelude definitions/structures/classes after generated-helper exclusion | 112 |
| Definitions cited by at least three Tier-B endpoints | 196 |
| Overlap | 38 |
| **Load-bearing union** | **270** |
| Direct reverse-citation rows for that union | 17,672 |
| Theorem-statement discovery candidates | 7,449 |
| Load-bearing rows without a theorem-statement candidate | 8 |

The arithmetic is exact: `112 + 196 - 38 = 270`. The union has 258
definitions, 11 structures, and one class. Its reason split is 74
Prelude-only, 158 Tier-B-only, and 38 in both inputs. The complete row sets
are the [load-bearing ledger](logs/recert_definition_load_bearing.tsv),
[reverse citations](logs/recert_definition_reverse_citations.tsv), and
[candidate inventory](logs/recert_definition_nontriviality_candidates.tsv).

Candidate citations are discovery metadata, never automatic evidence.

## Fail-closed semantic review

The current register was generated by
[recert_v7_review.py](scripts/recert_v7_review.py) under
[contract version 2](review/V7_DEFINITION_REVIEW_PROTOCOL.md). It accepts:

- `VERIFIED_CITATION` only when the chosen theorem is still in the current
  candidate inventory, has theorem kind and only standard axioms in fresh V4,
  re-anchors to one current source declaration, and both the target and
  citation kernel types exactly match the earlier reviewed statement
  snapshots;
- `VERIFIED_WITNESS` only when a current named theorem directly mentions the
  exact audited definition in its kernel type, its exact source and collector
  logs both complete with exit 0, its source/log contain no executable
  `sorry`/`admit`/`sorryAx`, and its collected axioms are contained in
  `{propext, Classical.choice, Quot.sound}`; or
- `UNVERIFIED_SANITY` only with an explicit current rationale and finding;
  the final register does not use this fallback.

No old machine metadata is inherited. Earlier semantic packets are used only
as reviewer candidates and are accepted only after the exact current
target/citation type gates, current source re-anchoring, and fresh V4 check.

| Review shard | Rows | Citation | Witness | Unverified |
|---|---:|---:|---:|---:|
| [Shard 1](review/recert_v7_definition_review/v7_definition_review_shard_01.tsv) | 68 | 51 | 17 | 0 |
| [Shard 2](review/recert_v7_definition_review/v7_definition_review_shard_02.tsv) | 68 | 59 | 9 | 0 |
| [Shard 3](review/recert_v7_definition_review/v7_definition_review_shard_03.tsv) | 67 | 58 | 9 | 0 |
| [Shard 4](review/recert_v7_definition_review/v7_definition_review_shard_04.tsv) | 67 | 60 | 7 | 0 |
| **Total** | **270** | **228** | **42** | **0** |

The [manifest](review/recert_v7_definition_review/v7_definition_review_manifest.tsv)
binds every load-bearing row to exactly one shard. The
[semantic decision register](review/recert_v7_semantic_decisions.tsv)
records the fresh 42 positive witness judgments and no negative disposition.
The [final summary](review/recert_v7_definition_review/recert_v7_definition_review_summary.txt)
and [validation transcript](logs/recert_v7_definition_review_validation.txt)
record `final_ready=true`, zero unreviewed rows, zero validation problems,
and `result=PASS`. The summary records `report_verdict_under_R6:
PASS-WITH-NOTES` and no residual finding. The validator PASS establishes
evidence/register integrity; the three informational observations below
determine this report's `PASS-WITH-NOTES` verdict.

### Compiled witness evidence

The witness source
[RecertV7Nontriviality.lean](scripts/witnesses/RecertV7Nontriviality.lean)
contains 37 named theorems. Five theorems directly support multiple related
definitions, producing 42 definition-to-witness evidence rows.

The exact source replay completed with exit 0 in 69.171 seconds, no error, and no
“declaration uses `sorry`” warning. The separate collector emitted exactly 37
unique theorem rows in 66.047 seconds, directly measured each theorem's type
dependencies, and found only the three permitted standard axioms. In
particular, the `SBMEdge`
witness retains the exact abbreviation as a direct type dependency and also
proves two concrete edges unequal; the combined raw-MGF witness separately
retains both `HDP.SubGaussian` and `HDP.SubExponential`.

Evidence:

- [exact witness source log](logs/recert_v7_nontriviality_witness_build.log);
- [37-row collector log](logs/recert_v7_nontriviality_witness_collector.log);
- [42-row witness evidence ledger](logs/recert_definition_witness_evidence.tsv);
- local collector source
  `.audit_work/verification/RecertV7NontrivialityCollector.lean`; and
- [final register build](logs/recert_v7_definition_review_command.log) and
  [read-only check](logs/recert_v7_definition_review_check.log), which
  completed in 83.666 and 36.206 seconds respectively, both with exit 0.

The nine-test
[review-framework calibration](logs/recert_v7_review_framework_tests_final.log)
proves that a candidate cannot self-promote, the final gate rejects an
unreviewed row, malformed/missing/duplicate evidence is rejected, and a
planted witness closed by `sorry` is rejected. The independent
[definition analyzer self-test](logs/recert_definition_sanity_selftest.log)
checks current path mappings, verdict precedence, and unreferenced and
self-reference-only dead-code plants.

## Residual semantic-evidence closure

The final pass closes all 10 former `UNVERIFIED_SANITY` rows:

| Definition | Compiled semantic evidence |
|---|---|
| `HDP.Chapter8.booleanClassUniformDeviation` | A singleton nonempty Boolean class with one sample has deviation exactly 1. |
| `HDP.Chapter8.canonicalProcessEDistance` | A Bool-indexed canonical Gaussian process has distance exactly 1 between its two indices. |
| `HDP.Chapter9.DvoretzkyMilmanSetConclusion` | The unit closed ball satisfies the 1/1 sandwich and fails when the outer radius is 0. |
| `HDP.Chapter9.setWidthEffectiveDimension` | The pair `{0,e₀}` has positive value while the singleton `{0}` takes the zero-diameter branch. |
| `HDP.HasSubGaussianIncrementsWith` | A canonical Gaussian process satisfies the predicate at `sqrt (8/3)` and fails at scale 0. |
| `HDP.RandomMatrix.IndependentEntries` | Product Bernoulli coordinates are independent, while duplicated Bernoulli entries are not. |
| `HDP.RandomMatrix.SubGaussianEntries` | A nonconstant Unit-by-Unit standard-Gaussian matrix has sub-Gaussian entries. |
| `HDP.SubExponential` | The zero observable satisfies the raw predicate under unit Dirac mass and fails under mass 3. |
| `HDP.SubGaussian` | The same exact-MGF contrast separates unit Dirac mass from mass 3. |
| `HDP.SubGaussianVector` | The identity standard-Gaussian vector in one dimension is nonconstant and sub-Gaussian in every direction. |

The full per-row judgments are in the semantic decision register and final
shards. The source replay, witness collector, and final register build/check
all complete with exit 0.

## Dead-code reachability sweep

The dead-code sweep is deliberately informational. It finds project
declarations with no incoming direct type/value dependency and then applies
four documented exclusions:

| Population or exclusion | Rows |
|---|---:|
| Zero-reverse declarations before exclusions | 4,280 |
| Compiler-generated/internal | 1,567 |
| Exercise declarations | 473 |
| Deliberately terminal Tier-B results | 200 |
| Root/import aggregators | 43 |
| **Excluded total** | **2,283** |
| **Remaining `DEAD_CODE_CANDIDATE` rows** | **1,997** |

The arithmetic reconciles exactly: `4,280 - 2,283 = 1,997`. The row-level
[dead-code sweep](logs/recert_definition_dead_code_sweep.tsv) lists every
candidate and every excluded declaration with its reason.

The environment calibration plant with no incoming edge has `(self, other) =
(0, 0)` and is classified dead; the referenced plant has `(0, 1)` and is
classified live. The production Python self-test separately checks a
self-reference-only plant. A dead-code candidate is not a deletion
recommendation: it can be a public API endpoint or a source-faithful terminal
result.

## Re-run commands

Run from the project root:

```bash
python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py \
  --log HighDimensionalProbability/Verification/logs/recert_definition_sanity_selftest.log -- \
  python3 -B HighDimensionalProbability/Verification/scripts/definition_sanity.py self-test

python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py \
  --log HighDimensionalProbability/Verification/logs/recert_v7_review_framework_tests_final.log -- \
  python3 -B HighDimensionalProbability/Verification/scripts/test_v7_definition_review.py
```

```bash
python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py \
  --heartbeat-seconds 45 \
  --log HighDimensionalProbability/Verification/logs/recert_definition_sanity_build.log -- \
  ~/.elan/bin/lake env lean \
    -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false \
    .audit_work/verification/DefinitionSanityRecertification.lean

python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py \
  --log HighDimensionalProbability/Verification/logs/recert_v7_definition_analyze_command.log -- \
  python3 -B HighDimensionalProbability/Verification/scripts/definition_sanity.py analyze \
    --v6-endpoints HighDimensionalProbability/Verification/logs/recert_v6_tier_b_endpoints.tsv \
    --v4-audit HighDimensionalProbability/Verification/logs/recert_axiom_audit.tsv
```

The analyzer command exits 2 before manual review by design; inspect
`[hard_failures]` and continue only when it says `(none)` and module coverage
passes.

```bash
python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py \
  --log HighDimensionalProbability/Verification/logs/recert_v7_nontriviality_witness_build.log -- \
  ~/.elan/bin/lake env lean \
    -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false \
    HighDimensionalProbability/Verification/scripts/witnesses/RecertV7Nontriviality.lean

python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py \
  --log HighDimensionalProbability/Verification/logs/recert_v7_nontriviality_witness_collector.log -- \
  ~/.elan/bin/lake env lean \
    -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false \
    .audit_work/verification/RecertV7NontrivialityCollector.lean
```

```bash
python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py \
  --log HighDimensionalProbability/Verification/logs/recert_v7_definition_review_command.log -- \
  python3 -B HighDimensionalProbability/Verification/scripts/recert_v7_review.py

python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py \
  --log HighDimensionalProbability/Verification/logs/recert_v7_definition_review_check.log -- \
  python3 -B HighDimensionalProbability/Verification/scripts/recert_v7_review.py --check
```

The final two commands must both exit 0 with 270 rows, no unreviewed row,
`final_ready=true`, zero problems, and `result=PASS`.

## Findings

| ID | Severity | Finding |
|---|---|---|
| V7-F1 | INFO | The current environment exactly covers all 223 expected modules; its 15,022 constants and 1,448,224 unique dependency edges pass every topology and V4-integrity check. |
| V7-F2 | INFO | The calibrated direct-reachability sweep retains 1,997 `DEAD_CODE_CANDIDATE` rows after 2,283 documented exclusions. |
| V7-F3 | INFO | All 270 rows have explicit positive dispositions: 228 citations pass exact current type/source/V4 gates, and 42 definitions have clean evidence from 37 named witnesses using only the permitted axioms. |

## Limitations

1. The load-bearing threshold counts direct references from the 519 V6
   theorem endpoints. It does not infer semantic importance from transitive
   dependency paths.
2. The machine gates prove citation identity, currentness, source anchoring,
   and axiom cleanliness. The claim that a selected theorem semantically
   excludes degeneration remains review-tier judgment.
3. The 37 named witnesses establish nontriviality for 42 definitions, not
   every definition in the environment.
4. Dead-code status uses incoming direct type/value references only. Public
   endpoints and intentionally terminal book theorems can legitimately have
   no internal consumer, so the 1,997 rows require source-level triage before
   any maintenance action.
5. V7 checks Lean-level definition sanity, not fidelity of the definitions
   to the book's prose.
