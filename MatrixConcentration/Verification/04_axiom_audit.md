# V4 — Universal axiom audit

**Verdict: PASS**

**Tier: machine**

**Finding count: C=0 M=0 m=0 I=0**

## Guarantee

Every declaration loaded from a `MatrixConcentration` module depends on at
most the permitted logical axioms `propext`, `Classical.choice`, and
`Quot.sound`. No loaded declaration depends on `sorryAx`,
`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, or a custom
axiom.

This is stronger in scope than the source README's endpoint claim: it covers
definitions, theorem helpers, compiler-generated declarations, and mangled
private declarations, not only the Book → Lean table.

## Method

From the project root:

```sh
~/.elan/bin/lake env lean --version \
  > MatrixConcentration/Verification/logs/axiom_lean_version.log 2>&1
python3 MatrixConcentration/Verification/scripts/source_manifest.py check
python3 MatrixConcentration/Verification/scripts/import_graph.py
bash MatrixConcentration/Verification/scripts/compile_calibration_plants.sh
/usr/bin/time -p ~/.elan/bin/lake env lean \
  -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false \
  MatrixConcentration/Verification/scripts/axiom_audit.lean \
  > MatrixConcentration/Verification/logs/axiom_audit_compile.log 2>&1 &
v4_audit_pid=$!
wait "$v4_audit_pid"
python3 MatrixConcentration/Verification/scripts/analyze_axioms.py
```

`compile_calibration_plants.sh` regenerates the controls before compiling
them, including the public/private `sorryAx` plant. The import-graph refresh
supplies the analyzer's independently measured 15-module target set.

The Lean harness imports the root module, walks every constant in
`env.constants`, obtains its defining module with `Environment.getModuleIdxFor?`,
and retains every constant whose module root is `MatrixConcentration`. It does
not discard internal names or names beginning `_private.`. For each retained
name it calls Lean 4.31's public `Lean.collectAxioms` API and writes the result
directly to a TSV file.

The harness separately dumps every loaded module whose root is
`MatrixConcentration`. The analyzer compares that set with V2's 15-file module
inventory, preventing a forgotten import from yielding a silent partial audit.

### Positive calibration

`make_calibration_plants.py` creates
`.audit_work/AxiomCalibration.lean`, containing one public and one private
theorem proved with `sorry`. The identical `collectAxioms` mechanism reports
`sorryAx` for both:

- `VerificationPublicAxiomCalibration`;
- mangled
  `_private.«.audit_work».AxiomCalibration.0.verificationPrivateAxiomCalibration`.

This proves that the collector neither misses public placeholders nor silently
filters private declarations.

## Results

| Measurement | Result |
|---|---:|
| Loaded project modules reconciled | 15 / 15 |
| Declarations audited | 2,213 |
| Mangled private declarations included | 137 |
| Definitions | 166 |
| Theorems/proof constants | 2,047 |
| Axiom-set exceedances | 0 |
| `sorryAx` dependencies | 0 |
| Native-reduction/compiler-trust dependencies | 0 |
| Declared `axiom` constants | 0 |
| Declared `opaque` constants | 0 |

The root import-only module has no constants of its own; its presence in the
15-module header set and all 14 constant-bearing module counts are recorded.
The axiom-set distribution is:

| Transitive axiom set | Declarations |
|---|---:|
| none | 43 |
| `Quot.sound` | 2 |
| `propext` | 258 |
| `Quot.sound`, `propext` | 130 |
| `Classical.choice`, `Quot.sound`, `propext` | 1,780 |

The environment total is intentionally larger than the README's source-level
public-keyword count because the environment includes private and
compiler-generated proof/declaration constants. V9 performs the independent
source-keyword recount and endpoint reconciliation.

The 137 mangled-private environment constants are likewise not a count of
source declarations: V7's lexical inventory finds 82 private source
declarations, while V4 also retains generated private auxiliaries. The
private and internal/generated categories can overlap and are not additive.

### Current post-correction census

After the exact removal of the two rejected declarations, the deterministic
corrected totals are bound to source-manifest digest
`38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89`.
They reconcile 15/15 modules and audit 2,213
declarations with zero axiom-set exceedances, zero `sorryAx` dependencies,
zero native-reduction/compiler-trust dependencies, and zero project-declared
axioms or opaques. Both public and private positive controls still report
`sorryAx`. No new finding arose, so the verdict remains PASS. The V4 evidence
was regenerated inside fresh aggregate
`8212cc84-aad8-4abc-b0df-b68fd3241112`, which passed with 2,213 audited
constants and zero exceedances against verification-input digest
`119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`.
The aggregate recorded 23 `START`, 23 `PASS`, zero `FAIL`, and zero `SKIP`;
its log SHA-256 is
`81b8bb7fa4f415ba1f98e4f5d143390c697bce5e9474ba2464e7a39e303c30b8`.
The independent final lifecycle checker subsequently passed with zero
problems, 14/14 final-claims files, and no writer lock or finalization guard
present.

## Findings

None.

## Raw evidence

- [`logs/axiom_audit.tsv`](logs/axiom_audit.tsv) — one row for every audited
  declaration.
- [`logs/axiom_modules.txt`](logs/axiom_modules.txt) — 15 loaded project
  modules.
- [`logs/axiom_summary.txt`](logs/axiom_summary.txt) and
  [`logs/axiom_summary.json`](logs/axiom_summary.json) — validated totals and
  distributions.
- [`logs/axiom_exceedances.tsv`](logs/axiom_exceedances.tsv) — header-only
  zero-exceedance result.
- [`logs/axiom_calibration.tsv`](logs/axiom_calibration.tsv) — public/private
  `sorryAx` controls.
- [`logs/axiom_audit_compile.log`](logs/axiom_audit_compile.log) — complete
  harness run and timing.
- [`logs/axiom_lean_version.log`](logs/axiom_lean_version.log) — Lean version
  sanity check captured from the canonical project root.
- [`logs/source_manifest.txt`](logs/source_manifest.txt) — the exact
  20-input source and claims snapshot certified by this rerun.
- [`logs/verification_input_manifest_summary.txt`](logs/verification_input_manifest_summary.txt)
  — the final 147-file verification-input snapshot, SHA-256
  `119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`.
- [`logs/run_all.log`](logs/run_all.log) and
  [`logs/run_all_status.log`](logs/run_all_status.log) — the fresh aggregate
  regeneration and source/input-bound PASS status.
- [`logs/final_lifecycle_check.txt`](logs/final_lifecycle_check.txt) — terminal
  lifecycle/report acceptance certificate: `problems=0`, `result=PASS`, final
  claims manifest 14/14, and lock/guard checks clear.

## Limitations

This audit trusts the Lean kernel and the pinned Mathlib/Batteries dependency
set as axiomatic bedrock. `Lean.collectAxioms` establishes logical dependency,
not whether a theorem's statement is useful or non-vacuous.

An environment audit cannot see a never-imported file. V2 proves that there
are no such project files, and V5 independently scans the complete physical
file-walk universe.

`Lean.collectAxioms` is also structurally blind to a theorem `P → Q` whose
premise `P` is simply never discharged: assuming a proposition introduces no
non-standard axiom. That broader conditional-interface question is outside
V4's guarantee.
