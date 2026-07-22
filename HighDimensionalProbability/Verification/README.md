# HighDimensionalProbability mechanical soundness verification

> **GitHub publication scope:** this checkout contains the verification
> scripts and Markdown reports only. Raw logs, inventories, generated
> TSV/JSON/text evidence, curation inputs, transient run state, and source-side
> appendix/human-review records remain in the local project archive. Paths to
> those omitted artifacts are retained as
> provenance references and are not expected to resolve in this curated
> checkout, which is therefore not a self-contained replay bundle. Files under
> `archive/` and generated review packets remain frozen historical evidence and
> retain the paths recorded when they were produced.

> **Round 11 status:** the Exercise/record layout change is applied and
> certified, but the full mechanical replay is intentionally deferred because
> the owner has additional changes to make. Unless a Round-11 paragraph says
> otherwise, the completed V1--V10 verdicts below remain Round-10 evidence;
> the interrupted fresh V4 shard was not merged or installed.

## 1. Purpose and provenance

This is the active index for the final post-removal V1--V10 re-certification,
completed on 2026-07-21 in America/New_York with Lean 4.31.0, Lake
5.0.0-src+68218e8, and the pinned Mathlib revision recorded in section 9. The
numbered V1--V10 documents are verification checks, not correction-pass
numbers. The superseded pre-removal index is preserved verbatim as
[README.pre-recertification.md](archive/README.pre-recertification.md); it is
historical evidence rather than a description of the active source tree.
This is the mechanical soundness pass (prompt 06 in the series; this run is
the post-Round-8 re-certification), followed by the final-correction
post-removal replay.

## 2. Overall soundness statement

For the source snapshot identified in section 9, all 222 physical library files belong to checked build surfaces, the complete 223-module environment elaborates, and all 15,022 project declarations were audited. There is no project axiom or unledgered checking bypass: only the 228 marked Exercise leaves use `sorryAx`, and every other axiom dependency is among `propext`, `Classical.choice`, and `Quot.sound`. V6 found no vacuous theorem in 779 review assignments; V7 gives positive evidence for all 270 load-bearing definitions; V8 covers the complete source surface, has zero `docBlame`, and retains 68 INFO-only API, naming, or automation advisories; V9 finds no actionable mismatch in the 611-row publication map; and V10 finds no undisclosed published result resting on a never-discharged project condition. These guarantees are conditional on the Lean kernel and hash-pinned dependencies. The explicit boundaries are the 228 Exercise proofs, the excluded source scopes in section 6, the 68 quality advisories, and ten disclosed conditional infrastructure items used only by unpublished helpers.

## 3. Glossary

| Term | Plain-language meaning |
|---|---|
| `sorry` / `sorryAx` | `sorry` is an unfinished Lean proof; compiled declarations that use it carry the detectable kernel dependency `sorryAx`. |
| Axiom | A primitive assumption accepted without a proof inside the audited project. |
| Three standard axioms | `propext`, `Classical.choice`, and `Quot.sound`; these are the only non-`sorryAx` axiom dependencies permitted by this audit. |
| Kernel-checked | Lean's small trusted checker accepted the elaborated declaration and all referenced proof terms. |
| Vacuous theorem | A formally true statement whose assumptions or definitions accidentally make it empty, impossible, or trivial. |
| Orphan module | A physical source file that no declared build surface imports or builds. |
| Escape hatch | A source construct that can bypass, weaken, or move work outside ordinary kernel checking. |
| Trust path | The chain from source through Lean, Lake, dependencies, scripts, and recorded evidence on which a claim relies. |
| Witness | A compiled concrete example or behavior theorem showing that a definition is not hollow or degenerate. |
| Ledgered | Explicitly disclosed in a named project record, with its status and limitation kept consistent with the verification evidence. |

## 4. Scope and non-goals

The FILE-WALK UNIVERSE is every physical `.lean` file under the source
directory `HighDimensionalProbability/`, excluding
`HighDimensionalProbability/Verification/**`, together with every physical
`.lean` file under the real project-root `MatrixConcentration/` directory. It
contains 212 HDP files and 10 MatrixConcentration files, for 222 physical
library files. The separate root aggregator `HighDimensionalProbability.lean`
makes 223 environment modules. The verified build surfaces are
`HighDimensionalProbability`, the glob-built `MatrixConcentration` package,
and the explicitly isolated `HighDimensionalProbability.Appendix` closure.

All 67 exercise source files are physically grouped below
`HighDimensionalProbability/Exercise/Chapter1` through `Chapter9`; no legacy
`ChapterN/Exercise` source directory remains. The
[reorganization delta certificate](logs/exercise_reorganization_delta.log)
binds this tree to the Round-10 source manifest and proves that the move changed
only required import tokens and four path-only comments, with no declaration
namespace, statement, or proof-body change.

Verification files and `.lake/**` are excluded from library counts. The
separate scratch surface contains 46 classified Lean files: 9 under `tmp/`
and 37 under `.audit_work/` (36 under `.audit_work/verification/` plus the
legacy `.audit_work/READMEProvedAxioms.lean`). The authenticated manifest contains
the 222 physical library files, the root aggregator, and three Lake/toolchain
pin files, for 226 entries.

The active whole-book projection has 835 conclusions: 769 core-formalized,
66 Appendix-proved, and 0 deferred/source-limited. The Appendix registry has
14/14 active source-faithful targets; its aggregator has 15 direct imports,
including one retained Borell domain-support module that is infrastructure
rather than a target.

This folder checks build coverage, placeholders, axioms, trust surfaces,
selected semantic failure modes, quality warnings, published
machine-checkable claims, and conditional interfaces. It does not prove that
every Lean statement matches the book's prose, solve the 228 exercises, or
re-audit the Lean kernel and dependency internals. Book-faithfulness and the
scope decision are recorded separately in [REVIEW_NOTES.md](REVIEW_NOTES.md),
[FAITHFUL_PROOFREAD_REPORT.md](archive/FAITHFUL_PROOFREAD_REPORT.md),
[CORRECTION_LEDGER.md](CORRECTION_LEDGER.md), and the controlling
[FINAL_CORRECTION_REPORT.md](FINAL_CORRECTION_REPORT.md).

## 5. V1--V10 verification index

Finding counts are ordered **Critical / Major / Minor / Info**. Machine tiers
are reproducible computations. Review tiers contain source-level mathematical
judgments. Mixed tiers combine both; their successful verdicts do not turn
review judgments into kernel proofs.

| # | Verification | What it guarantees | Tier | Verdict | Findings (C/M/m/I) | Report |
|---|---|---|---|---|---|---|
| V1 | Build integrity | The combined HDP/MatrixConcentration and isolated Appendix targets both build cleanly from the certified no-build-artifact copy; the complete warning-instance inventory is informational and separately classified. | Machine | PASS-WITH-NOTES | 0/0/0/1 | [V1 report](01_build_integrity.md) |
| V2 | Import-graph completeness | All 222 physical files are on declared build surfaces; the 223-node environment has no unresolved local import, cycle, duplicate path, trust-path deviation, or orphan. | Machine | PASS | 0/0/0/0 | [V2 report](02_import_graph.md) |
| V3 | Placeholder census | The only unfinished proofs are exactly 228 marked Exercise leaves in 46 files, and the textual and kernel inventories reconcile one-to-one. | Machine | PASS-WITH-NOTES | 0/0/0/1 | [V3 report](03_sorry_audit.md) |
| V4 | Axiom audit | All 15,022 declarations, 80,919 telescope binders, and 1,448,224 direct type/value dependency edges were checked; there is no project axiom, nonstandard non-`sorry` axiom, or unledgered `sorryAx`. | Machine | PASS-WITH-NOTES | 0/0/0/1 | [V4 report](04_axiom_audit.md) |
| V5 | Escape-hatch audit | The 222-file library has no executable checking bypass or high-risk meta construct; 238 executable trust-surface hits, 16 exported instances on external carriers, and all 46 scratch files are classified. | Machine | PASS-WITH-NOTES | 0/0/0/4 | [V5 report](05_escape_hatches.md) |
| V6 | Vacuity and triviality | All 779 review assignments are `OK`; the mandatory 702-row union resolves to 519 unique theorem endpoints, and all 103 Tier-C rows have compiled witnesses or exact clean citations. | Mixed: machine sweep and compiled sample; review close-reading | PASS | 0/0/0/0 | [V6 report](06_vacuity_triviality.md) |
| V7 | Definition sanity | All 270 load-bearing rows have positive evidence: 228 exact-gated citations and 42 witness rows supported by 37 named theorems; 1,997 dead-code candidates remain informational. | Mixed: machine census and witnesses; review dispositions | PASS-WITH-NOTES | 0/0/0/3 | [V7 report](07_definition_sanity.md) |
| V8 | Linter and quality | The complete 222-file surface was covered: 8,662 declarations examined, 6,360 generated declarations, and 68 INFO advisories (48 unused-argument, 13 simp-normal-form, 4 def/lemma-form, 2 naming, and 1 simp-commutativity); `docBlame` is clean after 97 documentation repairs. | Machine | PASS-WITH-NOTES | 0/0/0/3 | [V8 report](08_linter_report.md) |
| V9 | Published claims | The 66-row claim ledger has 60 `MATCH`, 0 stale, 0 overstated, and 6 static-scope `UNVERIFIABLE` rows; all 611 publication rows and 540 unique endpoint axiom sets reconcile. | Mixed: machine replay; review claim classification | PASS | 0/0/0/0 | [V9 report](09_readme_claims.md) |
| V10 | Conditional interfaces | All 352 named candidates are classified as 86 proved, 250 consumed-only, and 16 dead; all 4,734 inline rows are adjudicated, with ten INFO-only unpublished infrastructure items, removed-family absence, and retained finite-Chevet checks passing. | Mixed: machine census and joins; review adjudication | PASS-WITH-NOTES | 0/0/0/1 | [V10 report](10_conditional_interfaces.md) |

## 6. Active boundaries and known issues

The live proof-debt register has one class: 228 `KNOWN-LEDGERED` teaching
leaves, one executable `sorry` per marked exercise declaration in 46 files.
None occurs in Appendix or load-bearing support code. See the
[V3 reconciliation](logs/recert_v3_ledger_reconciliation.txt),
[V3 report](03_sorry_audit.md), and [V4 report](04_axiom_audit.md).

V10 additionally records ten source-disclosed conditional infrastructure
items with unpublished consumers only. They comprise
`BochnerRicciCertificate`; `MarkovSemigroupData` and its
`GammaTwoFlowCertificate`; four named energy, Gamma-two, Herbst, and
positivity predicates; `LogSobolev.dualEntropySet` and `dualEntropySetT`; and
the local `hDiffusion` helper for
`special_orthogonal_concentration_of_diffusion`. No published Tier-B result
depends on them. They are INFO-level interface facts, not missing published
proofs; see [V10](10_conditional_interfaces.md).

The authoritative publication boundary is:

> Every book item that remains in the 611-row publication map is covered. The only excluded scopes are equation (5.8), the arbitrary-set forms of Exercise 8.39(a) and Remark 8.6.3, and the Borell half of Example 3.4.6; their source-facing conditional or assumption-strengthened interfaces were removed on 2026-07-20. Finite-set Chevet results and Exercise 8.39(b) remain covered.

The excluded scopes are absent from active source and are not live issue
entries or completed theorem claims. The finite Gaussian--Chevet upper
theorems retain their visible `0 ∈ T` hypothesis; the arbitrary-set reverse
theorem for Exercise 8.39(b) remains proved.

## 7. Findings summary

The ten reports contain 14 findings: 0 Critical, 0 Major, 0 Minor, and 14
Info. Rows are sorted by severity.

| Finding | Severity | One-line summary |
|---|---|---|
| V1-F1 | INFO | Successful build logs preserve a complete informational warning-instance inventory; replayed dependency warnings are not unique source defects. [V1 report](01_build_integrity.md#findings) |
| V8-F1 | INFO | Full package lint reports 68 API, naming, and automation advisories; exact row adjudication found no mathematical, proof-closure, documentation, or coverage defect. [V8 report](08_linter_report.md#findings) |
| V8-F2 | INFO | V1's build-warning population is an informational replayed-instance view; the actionable 97-row missing-docstring set was repaired in Round 10. [V8 report](08_linter_report.md#findings) |
| V3-F1 | INFO | Exact proof debt is 228 marked, ledgered Exercise leaves in 46 files; source and kernel rows reconcile one-to-one. [V3 report](03_sorry_audit.md#findings) |
| V4-F1 | INFO | The sole project-origin opaque is the internal wrapper generated by `irreducible_def greedyOwnerIndex`; it uses standard axioms only. [V4 report](04_axiom_audit.md#findings) |
| V5-F1 | INFO | The 222-file library has no executable checking bypass or high-risk meta construct; the 46-file scratch surface is exhaustively classified. [V5 report](05_escape_hatches.md#findings) |
| V5-F2 | INFO | `greedyOwnerIndex` is the sole source `irreducible_def`; it supplies a checked value whose generated internal opaque uses standard axioms only. [V5 report](05_escape_hatches.md#findings) |
| V5-F3 | INFO | Relaxed implicit-name matching is disabled, while ordinary `autoImplicit` remains enabled as confirmed by a compiled probe. [V5 report](05_escape_hatches.md#findings) |
| V5-F4 | INFO | Sixteen exported instances on Mathlib-owned carriers are canonical, proof-irrelevant, or unique and are explicitly reviewed. [V5 report](05_escape_hatches.md#findings) |
| V7-F1 | INFO | The 223-module environment, 15,022 constants, and 1,448,224 dependency edges pass topology and V4-integrity gates. [V7 report](07_definition_sanity.md#findings) |
| V7-F2 | INFO | The calibrated reachability sweep retains 1,997 `DEAD_CODE_CANDIDATE` rows after 2,283 documented exclusions. [V7 report](07_definition_sanity.md#findings) |
| V7-F3 | INFO | All 270 load-bearing rows have positive evidence: 228 citations and 42 witness-backed rows from 37 named theorems. [V7 report](07_definition_sanity.md#findings) |
| V8-F3 | INFO | Coverage is complete: 8,662 examined declarations, all 68 lint rows across 30 modules, all 222 physical files, and zero excluded modules. [V8 report](08_linter_report.md#findings) |
| V10-F1 | INFO | Ten source-disclosed conditional infrastructure items have unpublished consumers only; no published Tier-B result depends on them. [V10 report](10_conditional_interfaces.md#findings) |

## 8. How to re-run

Run from the Lean project root. The manifest-first orchestrator is staged and
re-entrant. It validates preserved expensive evidence, aborts on source,
scratch, inventory, or record drift, and runs the machine-currentness gates:

```bash
python3 -B HighDimensionalProbability/Verification/scripts/run_logged.py \
  --log HighDimensionalProbability/Verification/logs/run_all.log -- \
  /bin/bash HighDimensionalProbability/Verification/scripts/run_all.sh --run
```

The orchestrator does not replace the review-tier V6, V7, and V10 procedures;
their standalone commands and controlling reports are listed below.

Expected runtimes on the recorded Apple M2 Pro are:

| Operation | Expected wall time |
|---|---:|
| Re-entrant `run_all.sh --run` with accepted expensive evidence present | allow up to about 45 minutes; fast cached replays can finish in under a minute; stage-marker reuse, evidence volume, and filesystem cache dominate |
| V1 from a copy with no project build artifacts | tens of minutes; use the exact measured times in [V1](01_build_integrity.md) |
| Fresh V4 two-shard raw environment collection | about 2.5 hours; analyzer about 1 minute |
| Fresh V7 raw harness plus source/evidence replays | about 25 minutes plus 3--4 minutes |
| Fresh V8 package lint | about 2--3 minutes |

V6 Tier-B, V7 disposition review, V9 claim interpretation, and V10
published-versus-unpublished adjudication require human review time and do not
have a meaningful push-button runtime.

| Verification | Focused currentness or reproduction entry point |
|---|---|
| V1 | `~/.elan/bin/lake build HighDimensionalProbability MatrixConcentration` and `~/.elan/bin/lake build HighDimensionalProbability.Appendix`; do not repeat the recorded one-use clean deletion. See [V1's sequence](01_build_integrity.md). |
| V2 | `python3 -B HighDimensionalProbability/Verification/scripts/import_graph.py --expect-count 222`; see [V2](02_import_graph.md). |
| V3 | Run the scanner, direct map, ledger reconciliation, and V3/V4 join in [V3's exact command block](03_sorry_audit.md). |
| V4 | Run the sequential two-shard collection, normalization, merge, install, self-test, and analysis sequence below; see [V4](04_axiom_audit.md). |
| V5 | Run the library and scratch scanners plus classifiers in [V5's exact command block](05_escape_hatches.md). |
| V6 | `python3 -B HighDimensionalProbability/Verification/scripts/check_v6_final.py --self-test` followed by `python3 -B HighDimensionalProbability/Verification/scripts/check_v6_final.py`; the Tier-A, Tier-B, and Tier-C regeneration commands are in [V6](06_vacuity_triviality.md). |
| V7 | `python3 -B HighDimensionalProbability/Verification/scripts/recert_v7_review.py --check`; the collector, intentional pre-review analyzer, witness replay, register build, and validation sequence is in [V7](07_definition_sanity.md). |
| V8 | `python3 -B HighDimensionalProbability/Verification/scripts/run_v8_package_lint.py --confirm-v7-complete`; see [V8](08_linter_report.md). |
| V9 | `python3 -B HighDimensionalProbability/Verification/scripts/v9_documentation_census.py --check` and `python3 -B HighDimensionalProbability/Verification/scripts/verify_readme_axioms.py --check-only`; see [V9](09_readme_claims.md). |
| V10 | Run `self-test`, `source-preview`, `run`, `analyze`, and `check` in that order with `v10_conditional_interfaces.py`; see [V10](10_conditional_interfaces.md). |

Round 11 adds one cross-cutting layout/current-path gate:

```bash
python3 -B HighDimensionalProbability/Verification/scripts/verify_reorganization_layout.py
```

It is also replayed inside the final `run_all.sh` consistency stage.

V4's actual sequential shard workflow is:

```bash
python3 -B HighDimensionalProbability/Verification/scripts/run_recert_v4_shard.py 0
python3 -B HighDimensionalProbability/Verification/scripts/normalize_recert_v4_shard_log.py /private/tmp/hdp_v4_78da87_shard0/axiom_audit_build.log
python3 -B HighDimensionalProbability/Verification/scripts/run_recert_v4_shard.py 1
python3 -B HighDimensionalProbability/Verification/scripts/normalize_recert_v4_shard_log.py /private/tmp/hdp_v4_78da87_shard1/axiom_audit_build.log
python3 -B HighDimensionalProbability/Verification/scripts/merge_pass07_v4_shards.py
python3 -B HighDimensionalProbability/Verification/scripts/install_recert_v4_merge.py
python3 -B HighDimensionalProbability/Verification/scripts/axiom_audit.py self-test
python3 -B HighDimensionalProbability/Verification/scripts/axiom_audit.py analyze \
  --v3-sorry-declarations HighDimensionalProbability/Verification/logs/recert_v3_sorry_declarations.tsv
```

The shard and merge runners refuse to overwrite existing
`/private/tmp/hdp_v4_78da87_shard0`,
`/private/tmp/hdp_v4_78da87_shard1`, and
`/private/tmp/hdp_v4_78da87_merged` directories;
consult V4 before starting a fresh collection. Removing preserved evidence is
not a verification step.

The two raw environment tables are collected afresh from source-manifest
digest
`78da8753a3367be0ae4c72df049a99f33723a7b22a1d08384714cc59d08853d4`.
The shard normalizers, merger, and installer all reject a different source
digest or harness hash; no pre-reorganization V4 table is relabelled or reused.

The complete standalone V10 sequence is:

```bash
python3 -B HighDimensionalProbability/Verification/scripts/v10_conditional_interfaces.py self-test
python3 -B HighDimensionalProbability/Verification/scripts/v10_conditional_interfaces.py source-preview
python3 -B HighDimensionalProbability/Verification/scripts/v10_conditional_interfaces.py run
python3 -B HighDimensionalProbability/Verification/scripts/v10_conditional_interfaces.py analyze
python3 -B HighDimensionalProbability/Verification/scripts/v10_conditional_interfaces.py check
```

V6 Tier-B close-reading, V7 semantic dispositions, V9 claim interpretation,
and V10 published-versus-unpublished adjudication are review-tier work. Their
scripts validate identity, coverage, joins, source anchors, digests, and
recorded dispositions; they do not recreate the human mathematical judgments
as kernel proofs.

## 9. Environment snapshot

| Item | Certified value |
|---|---|
| Run dates / timezone | 2026-07-19--21 / America/New_York |
| Operating system | macOS 15.6, arm64 (Darwin 24.6.0) |
| Hardware | Apple M2 Pro, 12 cores, 16 GB RAM |
| Python | 3.12.0 |
| Lean | 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783` |
| Lake | 5.0.0-src+68218e8 |
| Mathlib | input pin `v4.31.0`; revision `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| Source manifest | 226 entries; top-level digest `78da8753a3367be0ae4c72df049a99f33723a7b22a1d08384714cc59d08853d4` |

The complete environment capture is [logs/environment.txt](logs/environment.txt),
the authenticated source list is [logs/source_manifest.txt](logs/source_manifest.txt),
and the active manifest check is
[logs/source_manifest_recertification_check.txt](logs/source_manifest_recertification_check.txt).

## 10. Correct → re-verify iteration log

| Round | Date | Reverification and outcome |
|---:|---|---|
| 1 | 2026-07-18 report date; retrospective source-record evidence | Applied foundational F-01/F-02/F-04--F-11 corrections in dependency order, revalidated F-12/F-13, and rejected F-14 without an unwarranted edit. |
| 2 | 2026-07-18 report date; retrospective source-record evidence | Rebuilt the first affected downstream modules after the foundational definition repairs and closed the exposed proof/elaboration obligations. |
| 3 | 2026-07-18 report date; retrospective source-record evidence | Continued the definitional-ripple review through later Chapter 7 and Chapter 8 consumers, checking statement meaning even where compilation still succeeded. |
| 4 | 2026-07-18 report date; retrospective source-record evidence | Closed the remaining downstream obligations and replayed the affected whole-tree and Appendix build surfaces to green. |
| 5 | 2026-07-18 report date; retrospective source-record evidence | Rechecked every corrected or added statement and the five former core `PARTIAL` rows against the rendered original PDF; no new editable faithfulness defect survived. |
| 6 | 2026-07-18 report date | Rechecked every Pass-05 finding and all 25 non-INFO Pass-06 findings, repaired the Bernoulli helper, Berry--Esseen import, stale keys, and records, and assigned every historical row a disposition. |
| 7 | 2026-07-18 report date | Regenerated the import graph, V6/V7, placeholder, documentation, publication, build, and endpoint-axiom evidence for the pre-Round-8 tree. |
| 8 | 2026-07-19 | Historical pre-restructuring closure; superseded by the later source layout and retained only as provenance. |
| 9 | 2026-07-20 | Replayed the post-restructuring source through V1--V10 and the 611-row publication map, then removed three non-source-faithful interface families. Its narrative prematurely said the 97 package-lint `docBlame` rows were fixed; the active source still contained them. |
| 10 | 2026-07-21 | Fresh lint detected those 97 rows; all were repaired with one-line declaration docstrings across 25 files. The all-file [delta certificate](logs/round10_docstring_delta.log) proves zero nonblank non-documentation source change. The source manifest, clean builds, V3--V10 artifacts, consistency gate, full acceptance run, and immediate no-drift replay were regenerated against digest `bca641bd4c523754aa472b97cb1ed5638a6eb7361f99158a3f231a03a7446460`. The resulting population is 0 Critical / 0 Major / 0 Minor / 14 Info. |
| 11 | 2026-07-21 | Moved all 67 Exercise modules into `Exercise/Chapter1`--`Exercise/Chapter9`, kept every public `HDP.ChapterN.Exercise` declaration namespace stable, and moved current/historical records into the root/`Verification`/`Verification/archive` layout. The [exact reorganization certificate](logs/exercise_reorganization_delta.log) proves zero declaration or proof-body change and binds this intermediate tree to digest `78da8753a3367be0ae4c72df049a99f33723a7b22a1d08384714cc59d08853d4`. At the owner's request, the full path-sensitive replay was paused pending additional source changes; the interrupted V4 shard was not merged or installed. |

The [accepted first orchestration transcript](logs/run_all_first_acceptance.log)
and its [immediate no-drift replay](logs/run_all_no_drift_replay.log) are
preserved separately from earlier transient runs. A round is accepted only
when the manifest-first pipeline exits zero and its immediate replay changes
no authenticated input.
There are **10 completed correction/reverification rounds**; Round 11 is an
open layout/change phase whose combined replay is intentionally deferred until
the owner's additional changes are applied. Rounds 1--5 use retrospective
source-record evidence because no independent timestamped log was retained for
each of those sub-rounds.
