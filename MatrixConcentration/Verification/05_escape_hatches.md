# V5 — Escape-hatch and trust-surface scan

**Verdict: PASS-WITH-NOTES**

**Tier: mixed (machine lexical scan and review classification of reducibility/local-instance/`Fact` hits)**

**Finding count: C=0 M=0 m=0 I=4**

## Guarantee

Every Lean file in the complete physical source universe was scanned for the
specified kernel bypasses, checking-disabling options, elaboration-time
environment mutation, partial definitions, reducibility annotations, local
instance bindings, `Fact`, and meta-syntax shadowing.

No kernel-bypassing, checking-disabling, environment-mutating, partial, or
meta-syntax construct was found in active library code. The remaining
trust-surface constructs are completely inventoried below and are
informational.

## Method

All commands ran from the project root:

```sh
python3 MatrixConcentration/Verification/scripts/source_manifest.py check
python3 MatrixConcentration/Verification/scripts/make_calibration_plants.py
python3 MatrixConcentration/Verification/scripts/scan_escape_hatches.py calibration
python3 MatrixConcentration/Verification/scripts/scan_escape_hatches.py production
```

The scanner includes every `.lean` file physically below the project root and
excludes exactly `.lake/**`, `MatrixConcentration/Verification/**`, and
`.audit_work/**`: 15 files, comprising the root and 14 inner modules. This
physical sweep also covers a hypothetical never-imported file. Audit
harnesses, controls, non-Lean files, and macOS `Icon\r` junk are not library
input.

The same nested-comment-aware lexer used by V3 classifies every hit as code,
line comment, block comment, documentation comment, or string. The raw TSV
retains each hit with its path, location, lexical context, source line, and
severity/review classification.

The active-code pattern set covers:

- `axiom`, `opaque`, `native_decide`, `unsafe`,
  `@[implemented_by]`, `@[extern]`, and `@[csimp]`;
- every `set_option`, with special checks for `debug.skipKernelTC` and the
  `bootstrap.*` option family;
- `run_cmd`, `run_elab`, `#eval`, `initialize`, `modifyEnv`, `addDecl`, and
  `Environment.add`;
- `partial def`, `@[reducible]`, exact `local instance` declarations,
  proof-local `letI`/`haveI` bindings, and `Fact`;
- `macro`, `macro_rules`, `syntax`, `elab`, `elab_rules`, `notation`, and
  prefix/postfix/infix notation declarations. The additional syntax forms
  make the standard-token shadowing check conservative.

### Positive calibration

`.audit_work/EscapePlant.lean` contains an `axiom`, an `unsafe def`, a theorem
closed by `native_decide`, and a `run_cmd`. The production scanner's identical
machinery detected all four required patterns, plus the plant's benign
`set_option`. The calibration result is PASS.

## Results

### Prohibited and review-required constructs

| Construct class | Patterns | Active hits | Verdict |
|---|---|---:|---|
| Direct trust bypass | `axiom`, `opaque`, `native_decide`, `unsafe` | 0 | clean |
| Foreign/compiler implementation | `implemented_by`, `extern`, `csimp` | 0 | clean |
| Checking-disabling option | `debug.skipKernelTC`, `bootstrap.*` | 0 | clean |
| Elaboration-time environment mutation | `run_cmd`, `run_elab`, `#eval`, `initialize`, `modifyEnv`, `addDecl`, `Environment.add` | 0 | clean |
| Nontermination escape | `partial def` | 0 | clean |
| Meta-syntax / token shadowing | macro, syntax, elaborator, and notation forms | 0 | clean |

The lexical scan retained 19 inactive documentation-comment mentions: 14 uses
of “Fact” as a book label, three prose uses of “notation,” one prose use of
“prefix,” and one prose use of “norm axiom.” None is Lean syntax. Every
individual row and its `textual_mention` classification appears in
`logs/escape_hatch_scan.tsv`.

### `set_option` inventory

All 150 options are resource or linter settings; none disables checking:

| Option | Occurrences | Trust assessment |
|---|---:|---|
| `maxHeartbeats` | 64 | resource budget only |
| `linter.unusedSectionVars` | 83 | linter configuration only |
| `linter.unusedDecidableInType` | 1 | linter configuration only |
| `linter.unusedFintypeInType` | 1 | linter configuration only |
| `linter.unusedVariables` | 1 | narrowly scoped linter configuration with an adjacent API-faithfulness rationale |
| **Total** | **150** | **0 checking-disabling** |

### Reducibility and instance inventories

There are two reducibility annotations, both in
`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`:

| Line | Declaration | Review |
|---:|---|---|
| 222 | `entrywiseL1NormedAddCommGroup` | transparent alias of the explicitly constructed `entrywiseL1AddGroupNorm.toNormedAddCommGroup` |
| 2032 | `schattenOneNormedAddCommGroup` | transparent alias of the explicitly constructed `schattenOneAddGroupNorm.toNormedAddCommGroup` |

Neither annotation hides a proposition, proof, axiom, or computation; both
only expose a named bundled norm structure for definitional reduction.

The local-instance inventory contains no exact `local instance` declaration,
20 `letI` bindings, and 55 `haveI` bindings. All 75 are proof-local. Review of
the complete listing found that they install witnesses already established in
the surrounding proof: nonemptiness or emptiness after a case split, finite
dimensionality, probability/finite-measure structure, finite/discrete
topology, or invertibility derived from positive definiteness. None creates a
propositional shortcut or surprising global instance.

There is one active `Fact` occurrence, at
`Chapter5_SumOfPSDMatrices.lean:3446`. It packages the proved arithmetic
identity
`finrank (EuclideanSpace ℂ V) = (card V - 1) + 1` needed by an orthonormal-basis
constructor; its proof uses `finrank_euclideanSpace`, positivity of
`Fintype.card V`, and arithmetic. It does not assert an unproved fact and does
not escape the kernel.

### Auto-implicit status

The project `lakefile.toml` sets `relaxedAutoImplicit = false` and does not set
`autoImplicit`. Therefore `autoImplicit` remains at Lean's default `true`.
The relaxed-auto-implicit setting narrows which undeclared identifiers may be
auto-bound; it does not disable auto-binding. This is a recorded trust-surface
fact, not a soundness defect. V6 consumes it for the separate
auto-bound-implicit statement audit.

### Final post-correction re-certification

The scope-corrected source manifest currently has digest
`38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89`.
The previous calibrated lexical scan covered all 15 files and reported zero
prohibited or environment-mutating constructs, zero checking-disabling
options, and the complete benign inventory: 150 `set_option` commands, two
reducibility annotations, 75 proof-local instance bindings, and one proved
arithmetic `Fact`. The final lifecycle-bound replay inside fresh aggregate
`8212cc84-aad8-4abc-b0df-b68fd3241112` reproduced those results against
verification-input digest
`119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`.
It recorded 23 `START`, 23 `PASS`, zero `FAIL`, and zero `SKIP`; its log
SHA-256 is
`81b8bb7fa4f415ba1f98e4f5d143390c697bce5e9474ba2464e7a39e303c30b8`.
Removing the two theorem wrappers introduced no new trust-surface construct.
The independent final lifecycle checker subsequently passed with zero
problems, 14/14 final-claims files, and no writer lock or finalization guard
present.

## Findings

### V5-F1 — INFO — Benign source options are inventoried

The source has 150 `set_option` commands: 64 heartbeat budgets and 86 linter
settings. None sets `debug.skipKernelTC` or a `bootstrap.*` checking bypass.

### V5-F2 — INFO — Two narrow reducibility annotations

The two `@[reducible]` declarations are transparent aliases for explicitly
constructed bundled norm structures. Neither changes the trust path.

### V5-F3 — INFO — Proof-local instances and one proved `Fact`

The source has 75 proof-local `letI`/`haveI` bindings and one arithmetic
`Fact`. Complete contextual review found no manufactured proposition,
unjustified typeclass fact, or globally leaking local instance.

### V5-F4 — INFO — Auto-implicit binding remains enabled

`relaxedAutoImplicit = false`, while `autoImplicit` is not overridden and
therefore remains at its Lean default of `true`. V6 is responsible for
checking that this did not corrupt correspondence-table statements.

## Raw evidence

- [`logs/escape_hatch_scan.tsv`](logs/escape_hatch_scan.tsv) — every textual
  hit, including complete `letI`/`haveI`, `Fact`, reducibility, option, and
  documentation-mention context.
- [`logs/escape_hatch_scan.json`](logs/escape_hatch_scan.json) and
  [`logs/escape_hatch_summary.txt`](logs/escape_hatch_summary.txt) — universe,
  per-pattern totals, and result.
- [`logs/set_option_inventory.tsv`](logs/set_option_inventory.tsv) — all 150
  option commands with path, line, value, and checking-disabling flag.
- [`logs/escape_hatch_calibration.tsv`](logs/escape_hatch_calibration.tsv) and
  [`logs/escape_hatch_calibration.txt`](logs/escape_hatch_calibration.txt) —
  planted multi-pattern positive result.
- [`logs/autoimplicit_trust_surface.txt`](logs/autoimplicit_trust_surface.txt)
  — the lakefile-derived `relaxedAutoImplicit`/`autoImplicit` record.
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

This is a lexical trust-surface scan, not a replacement for kernel inspection.
V4 independently audits every loaded declaration's transitive axiom set, while
V2 establishes that all physical source files are imported. The scanner
recognizes nested Lean comments and strings but does not reproduce the full
Lean parser.

The absence of escape hatches does not establish that definitions are
non-degenerate or theorem statements non-vacuous; V6 and V7 address those
questions. The `autoImplicit = true` trust-surface fact is recorded here, but
the statement-by-statement auto-bound binder analysis belongs to V6.

Nor does this lexical scan decide whether an ordinary proposition or
typeclass premise is ever instantiated; that broader semantic question is
outside V5's guarantee.
