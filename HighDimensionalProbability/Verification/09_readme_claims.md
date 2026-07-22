# V9 — Published-claims and current-census cross-check

**Verdict: PASS**

## Scope

V9 checks the editable HighDimensionalProbability publications against the
post-removal source tree and its machine-readable inventories. It keeps two
census layers explicit:

- `review_census_838.{tsv,json}` is immutable historical evidence; and
- `review_census_835.{tsv,json}` is the active projection after the
  2026-07-20 conditional-interface removals.

The static claim audit reads the root and package READMEs,
`Verification/REVIEW_NOTES.md`, `Verification/CORRECTION_LEDGER.md`, the
active header of `APPENDIX_SUMMARY.md`,
`Appendix.lean`, the source tree, the publication map, both census layers,
the endpoint union, and V6's complete publication-map join. It does not invoke
Lean, Lake, Git, or the network. Dynamic build and kernel claims are joined
to their separately recorded V1/V4/V9 evidence.

The V9 MatrixConcentration scope remains read-only. The project contains ten
vendored MatrixConcentration Lean modules and no vendored self-record
documents; the distinct freestanding sibling is outside this report's claim
scope.

## Result

The generated [66-row claim ledger](review/recert_v9_documentation_census.tsv)
has:

| Verdict | Rows |
|---|---:|
| `MATCH` | 60 |
| `STALE` | 0 |
| `OVERSTATED` | 0 |
| `UNVERIFIABLE` | 6 |
| **Total** | **66** |

The six static-scope rows are not current claim defects:

| Scope limitation | Rows | Disposition |
|---|---:|---|
| Requested aliases `REVIEW_CENSUS.md` and `PLACEHOLDER_LEDGER.md` do not exist | 2 | The canonical frozen/current census artifacts, correction ledger, and V3 report are checked directly. |
| “All verified” publication wording | 2 | Static counts and the V6 join agree; endpoint resolution/axioms and PDF review are separate evidence. |
| Whole-tree and isolated-Appendix build claims | 2 | V9 does not replay builds; V1 supplies their source-bound exit evidence. |

There are zero present-tense stale claims, zero overstatements, and zero
actionable current mismatches. The deterministic
[summary](review/recert_v9_documentation_census_summary.txt) records the exact
ledger digest and every measured count.

## Frozen and active census layers

The frozen artifacts remain byte-authentic:

| Artifact | SHA-256 |
|---|---|
| `review_census_838.tsv` | `184f44ef33c9318450b9b31282c02850868cdafb93fe7ad722219acd7e6e1857` |
| `review_census_838.json` | `facc370aac1cd62dbcbbbe1bad54ff6175ea6768cda31111eb630aed1e5de284` |

Their historical split remains:

```text
838 = 768 core-formalized + 65 Appendix-proved + 5 deferred
```

Before the removal, the live Round 9 overlay had already moved Brownian, so
its current-state projection was
`838 = 768 core-formalized + 66 Appendix-proved + 4 deferred`. The frozen
65/5 split and the pre-removal live 66/4 split are therefore different
status layers, not conflicting arithmetic.

The active projection is a distinct generated artifact:

```text
835 = 769 core-formalized + 66 Appendix-proved + 0 deferred
```

It is exactly the frozen row-ID set minus:

- `census-bf1de680f35b52dc` — Borell half of Example 3.4.6;
- `census-628be74004e48217` — equation (5.8); and
- `census-939078c2ac4f78a5` — arbitrary-set Remark 8.6.3.

Two retained rows have explicit current dispositions:

- `census-8e50e84b6b82a573` is now Exercise 8.39(b),
  `core_formalized`, with only
  `HDP.Chapter8.exercise_8_39b_gaussian_chevet_reverse_arbitrary`; and
- `census-360c40946511e7a9` remains `appendix_proved` at
  `HDP.Chapter7.brownianReflectionPrinciple_external`.

The active chapter totals are
`11/63/71/96/117/111/47/82/122/115`, summing to 835. No active census
row is deferred or source-limited.

The complete live before→after measurements are:

| Surface | Before removal | Active |
|---|---:|---:|
| publication rows | 611 | 611 |
| unique published endpoints | 540 | 540 |
| valid conclusions | 838 | 835 |
| core-formalized conclusions | 768 | 769 |
| Appendix-proved conclusions | 66 | 66 |
| deferred/source-limited conclusions | 4 | 0 |
| registered Appendix targets | 17 | 14 |
| consolidated core target declarations | 5,630 | 5,625 |
| documented non-Appendix declarations | 6,078 | 6,073 |
| physical source files | 224 | 222 |

## Removed and retained interfaces

The static source audit confirms:

| Check | Result |
|---|---:|
| Deleted Lean files absent | 2/2 |
| Removed declaration names checked | 12 |
| Live non-Verification source references to those names | 0 |
| Active endpoint-union references to those names | 0 |
| Active-census endpoint references to those names | 0 |
| Borell domain-support declarations retained | 5 |
| Appendix direct imports | 15 |
| Active registered targets | 14 |
| Imports outside Appendix that reach the isolated Appendix | 0 |

The two finite theorem names
`HDP.Chapter8.exercise_8_39a_gaussian_chevet` and
`HDP.Chapter8.remark_8_6_3_gaussian_chevet` both remain and both visibly
bind `hzero : 0 ∈ T`. The arbitrary-set reverse theorem for Exercise 8.39(b)
and the source-faithful Brownian endpoint also remain.

`BorellConvexBody.lean` now exports only its normalized-law/domain support:
one definition and four theorems. It exports no universal marginal-tail or
`ψ₁` principle and no conditional specialization. Its aggregator import is
therefore infrastructure, not a fifteenth target.

The long reconstruction dossier below the
`Historical 17-target reconstruction record` heading in
`APPENDIX_SUMMARY.md` is explicitly historical. V9 reads present-tense
registry and coverage claims from the active header rather than treating the
pre-removal 17-target text as live state.

## Publication map and endpoint axioms

The curated publication map did not contain any of the three removed census
rows. Its measured surface remains:

| Measurement | Result |
|---|---:|
| correspondence rows | 611 |
| unique published endpoints | 540 |
| V6 publication rows | 611 |
| V6 rows with `OK` disposition | 611 |
| V6 rows with a source location | 611 |
| active endpoint-union names | 634 |

The endpoint harness is generated deterministically from those 611 README
rows. Its exact-currentness check validates the current README, generated
harness, raw Lean transcript, result TSV, summary, and V4 join. The preserved
endpoint result is:

| Measurement | Result |
|---|---:|
| parsed `#print axioms` results | 540 |
| project endpoints | 527 |
| external Mathlib endpoints | 13 |
| project endpoints absent from V4 | 0 |
| README/V4 axiom-set mismatches | 0 |
| endpoints using a nonstandard axiom | 0 |

The exact axiom-set distribution is:

| Exact set | Endpoints |
|---|---:|
| none | 1 |
| `Quot.sound` | 1 |
| `Quot.sound; propext` | 2 |
| `Classical.choice; Quot.sound; propext` | 536 |
| **Total** | **540** |

This establishes endpoint resolution and allowed-axiom consistency. The
separate PDF-grounded review supplies the semantic book-to-endpoint
faithfulness judgment.

## Declaration, documentation, and source counts

The current lexical measurements agree with both READMEs and the active
ledgers:

| Surface | Measured |
|---|---:|
| consolidated core target declarations | 5,625 |
| core theorems / lemmas / definitions | 2,862 / 1,608 / 1,155 |
| documented non-Appendix declarations | 6,073 / 6,073 |
| documentation theorems / lemmas / definitions | 3,107 / 1,610 / 1,356 |
| documentation files / issues | 101 / 0 |
| physical library files | 222 = 212 HDP + 10 MatrixConcentration |
| marked Exercise `sorry` proofs | 228 in 46 files |
| Appendix `sorry` / `admit` / `axiom` / `unsafe` / `native_decide` | 0 / 0 / 0 / 0 / 0 |

These are source-level declaration and file counts, not V4's elaborated
environment-constant denominator.

## Reproduction

Run from the project root:

```sh
python3 -B HighDimensionalProbability/Verification/scripts/v9_documentation_census.py
python3 -B HighDimensionalProbability/Verification/scripts/v9_documentation_census.py --check
python3 -B HighDimensionalProbability/Verification/scripts/verify_readme_axioms.py --self-test
python3 -B HighDimensionalProbability/Verification/scripts/verify_readme_axioms.py
python3 -B HighDimensionalProbability/Verification/scripts/verify_readme_axioms.py --check-only
python3 -B HighDimensionalProbability/Verification/scripts/v9_matrix_concentration_scope.py
python3 -B scripts/audit_docstrings.py --check
~/.elan/bin/lake build HighDimensionalProbability
~/.elan/bin/lake env lean HighDimensionalProbability/Chapter4_RandomMatrices.lean
```

Current static generation and exact-currentness both exit 0 with
`rows=66, MATCH=60, OVERSTATED=0, STALE=0, UNVERIFIABLE=6`.
The endpoint self-test and exact-currentness check both exit 0; the latter
reports 611 correspondence rows and 540 unique endpoints.
The two commands printed by the project READMEs were also executed literally:
the root build completed 8,670 jobs with exit 0, and the documented single-file
Chapter 4 command completed with exit 0. The single-file form does not inherit
the lakefile's linter set, as disclosed elsewhere in this report bundle.

Primary evidence:

- [current claim ledger](review/recert_v9_documentation_census.tsv) and
  [summary](review/recert_v9_documentation_census_summary.txt);
- [frozen 838 TSV](inventory/review_census_838.tsv) and
  [active 835 TSV](inventory/review_census_835.tsv);
- [static generation log](logs/recert_v9_documentation_census_generate.log)
  and [exact-currentness log](logs/recert_v9_documentation_census_check.log);
- [endpoint result TSV](logs/recert_v9_readme_axioms.tsv),
  [endpoint summary](logs/recert_v9_readme_axioms_summary.txt), and
  [endpoint exact-currentness log](logs/recert_v9_readme_axioms_check_only.log);
- [documentation audit](logs/recert_v9_docstring_audit.log); and
- [MatrixConcentration scope census](logs/recert_v9_matrix_concentration_scope.log);
- [printed root build command](logs/recert_v9_root_readme_build_command.log); and
- [printed single-file command](logs/recert_v9_main_readme_single_file_command.log).

## Findings

| ID | Severity | Finding | Evidence |
|---|---|---|---|
| None | None | No present-tense published self-claim mismatch or uncovered machine-checkable V9 claim was found. | Current 66-row claim ledger; 835 projection; 611-row endpoint evidence |

## Limitations

- V9 checks published claims and source/API identity. V1 owns build
  completion; V4 owns exhaustive environment axioms; V6 owns semantic
  vacuity review; V10 owns conditional-interface disclosure.
- The endpoint audit proves name resolution and axiom-set consistency. It
  does not independently reread all 611 source passages in the book PDF.
- The two requested Markdown aliases are absent; canonical machine-readable
  census and correction artifacts are used instead.
