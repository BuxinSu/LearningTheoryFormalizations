# V6 — Vacuity and triviality audit

**Verdict: PASS**

This current-tree recertification found no vacuous theorem. Automated Tier A
parsed every source declaration in the physical library surface and joined
every theorem telescope to the fresh V4 environment. Review-tier Tier B
close-read the fixed 611-row correspondence table, all 91 additional direct
census rows, the specified exercise samples, and the deterministic Tier-C
queue. Compiled Tier C then adjudicated the retained 50 fixed OK controls, a
reproducible 50-row random sample keyed to the last substantive source
snapshot, all three Tier-A escalations, and zero suspects.

The prior positive-Ricci conditional family, arbitrary-set Gaussian–Chevet
upper wrappers, and conditional Borell marginal specialization were removed
from the source tree before this recertification. V6 therefore treats those
removed conditional interfaces as absent scope rather than retaining stale
SUSPECT or assumption-strengthened rows. The finite zero-containing Chevet
upper results, unconditional arbitrary-set reverse Chevet results, and
convex-body normalized-law domain infrastructure remain in scope.

## Scope

The file-walk universe is every physical `.lean` file under
`HighDimensionalProbability/` union every physical `.lean` file under the real
project-root `MatrixConcentration/` directory. It excludes
`HighDimensionalProbability/Verification/**` and `.lake/**`.
`HighDimensionalProbability.lean` is treated separately as the one environment
root. Files in `tmp/*.lean` and `.audit_work/**/*.lean` are separately
classified scratch and are never counted as library source.

Book-faithfulness is outside V6. This report asks whether the current Lean
statements have jointly satisfiable hypotheses, substantive conclusions,
nondegenerate types and measures, and usable quantifier structure.

## Method

### Tier A — complete syntactic triage

[`v6_tier_a_scanner.py`](scripts/v6_tier_a_scanner.py) parses declarations and
flags contradictory or nearly contradictory numeric bounds, empty domains,
zero-cardinality finite domains, and syntactically trivial conclusions. It
also joins each parsed theorem to V4's exact type and binder-telescope dumps
to detect suspicious auto-bound implicit variables.

The detector was calibrated by 17 tests, including planted contradictory
bounds, `IsEmpty`, and trivial-conclusion positives. The final scan required
zero unparsed declarations and a complete, unambiguous V4 join. Every hit was
then reviewed against the H/C/T/Q checklist in the deterministic review
register.

Evidence:

- [calibration log](logs/recert_v6_tier_a_calibration.log)
- [final scan command log](logs/recert_v6_tier_a_final_scan.log)
- [final scan JSON](logs/recert_v6_tier_a_final.json)
- [full review register](review/recert_v6_tier_a_full_review.tsv)
- [full review summary](review/recert_v6_tier_a_full_review_summary.md)
- [review drift check](logs/recert_v6_tier_a_review_check.log)

### Tier B — fixed semantic close reading

The mandatory semantic union is exactly:

- all 611 rows of the public book-to-Lean correspondence table; and
- 91 direct-census endpoint rows not represented by that table.

The live review inventory has 835 rows. The 838-row file is retained only as
the frozen pre-removal snapshot; its three additional rows are precisely the
removed Borell, positive-Ricci, and arbitrary-set upper-Chevet scopes, and no
current Tier-B or Tier-C selection is drawn from them.

The main ledgers additionally contain 27 exercise-leaf samples—three per
Chapter 1–9—and the fixed 50-row Tier-C queue—five each for the Appetizer and
Chapters 1–9. Thus the complete close-reading assignment is 779 rows, while
the V7 handoff deliberately uses only the mandatory 702-row union.

Each row records:

1. whether its hypotheses admit a nondegenerate joint model;
2. whether its conclusion avoids totalization or junk-value collapse;
3. whether its typeclass, measure, and nonempty-space assumptions are sound;
4. whether its quantifier structure is usable; and
5. a source location and, where available, a downstream citation candidate.

The ledgers and deterministic read-only checks are:

| Assignment | Main | Supplement | Total | Result |
|---|---:|---:|---:|---|
| Appetizer–Chapter 4 | 318 | 24 | 342 | 342 OK |
| Chapters 5–7 | 193 | 14 | 207 | 207 OK |
| Chapters 8–9 | 177 | 53 | 230 | 230 OK |
| **Total** | **688** | **91** | **779** | **779 OK, 0 SUSPECT, 0 VACUOUS** |

Evidence:

- [current 835-row review census](inventory/review_census_835.tsv) and
  [frozen 838-row snapshot](inventory/review_census_838.tsv)
- [Appetizer–Chapter 4 ledger](review/v6_tier_b_ch0_4.tsv) and
  [supplement](review/v6_tier_b_supplement_ch0_4.tsv)
- [Chapters 5–7 ledger](review/v6_tier_b_ch5_7.tsv) and
  [supplement](review/v6_tier_b_supplement_ch5_7.tsv)
- [Chapters 8–9 ledger](review/v6_tier_b_ch8_9.tsv) and
  [supplement](review/v6_tier_b_supplement_ch8_9.tsv)
- [mandatory endpoint union](logs/recert_v6_tier_b_endpoints.tsv),
  [exclusions](logs/recert_v6_tier_b_endpoint_exclusions.tsv), and
  [summary](logs/recert_v6_tier_b_endpoint_summary.txt)

The mandatory endpoint builder selected 702 rows, expanded 744 declaration
references, and produced 519 unique project theorem endpoints. Its 124
explicit exclusions are 14 Mathlib endpoints and 110 project non-theorem
endpoints; no project theorem was silently dropped.

### Tier C — compiled named witnesses and exact citations

Tier C covers exactly 103 rows:

- five retained legacy fixed OK controls for each of the Appetizer and
  Chapters 1–9: 50;
- five additional reproducibly random OK controls for each of those ten
  chapters: 50;
- all Tier-A escalations: 3.

The random sample's stable semantic seed is
`83678e994eecf416759cb099d5e69f9d03c15921960d4f3b69d055a7a9e8fe27`,
the post-removal source-manifest digest before Round 10's documentation-only
correction. The current source digest is
`78da8753a3367be0ae4c72df049a99f33723a7b22a1d08384714cc59d08853d4`.
The [Round 10 delta gate](logs/round10_docstring_delta.log) compares all 222
library files plus the root aggregator and proves that the exact transition is
97 one-line declaration docstrings across 25 files, with zero nonblank
non-doc source change, producing digest
`bca641bd4c523754aa472b97cb1ed5638a6eb7361f99158a3f231a03a7446460`.
The subsequent [Exercise-reorganization delta gate](logs/exercise_reorganization_delta.log)
authenticates the transition from that digest to the current digest: all 67
exercise files move to `Exercise/Chapter1`--`Exercise/Chapter9`, with only
forced import and comment rewrites, zero declaration namespace/body changes,
and zero unexpected source changes. Re-drawing the semantic sample for either
certified nonsemantic transition would discard 46 already compiled review
controls without changing the population being reviewed. The sampler therefore
accepts this exact two-gate successor and retains the substantive baseline
digest as its seed.
For every canonical candidate row `r` in chapter `c`, it ranks
`SHA256(UTF8(seed + NUL + c + NUL + r.row_id))` ascending and takes the first
five without replacement. Eligibility starts from the complete OK Tier-B
population, without dropping external, Mathlib, or definition endpoints.
Rows whose entire resolved endpoint cell was already fixed-covered are
excluded; identical remaining endpoint cells are deduplicated by retaining
the lexicographically first row ID. The legacy controls themselves remain in
Tier C. The 779 unique ledger rows become 780 chapter-row sampling units
because one supplemental row spans both Chapters 8 and 9 and is placed in
each chapter's sampling population.

| Chapter | Full OK rows | Legacy rows | Fixed-only | Duplicate cell | Canonical frame | Selected |
|---|---:|---:|---:|---:|---:|---:|
| Appetizer | 17 | 5 | 5 | 0 | 7 | 5 |
| Chapter 1 | 60 | 5 | 5 | 0 | 50 | 5 |
| Chapter 2 | 73 | 5 | 5 | 6 | 57 | 5 |
| Chapter 3 | 93 | 5 | 6 | 1 | 81 | 5 |
| Chapter 4 | 99 | 5 | 11 | 16 | 67 | 5 |
| Chapter 5 | 88 | 5 | 9 | 9 | 65 | 5 |
| Chapter 6 | 47 | 5 | 5 | 6 | 31 | 5 |
| Chapter 7 | 72 | 5 | 12 | 12 | 43 | 5 |
| Chapter 8 | 120 | 5 | 10 | 15 | 90 | 5 |
| Chapter 9 | 111 | 5 | 6 | 15 | 85 | 5 |

The result was 91 compiled named witnesses, counted at the evidence-row
level, and 12 exact clean V4 direct-value citation rows. Those 91 witness rows
reference 93 distinct declarations: one fixed Chapter 3 row and one seeded
Chapter 7 row each have two endpoints and therefore record both of their
compiled witnesses. Every endpoint in a
multi-endpoint Tier-C cell is covered by a named witness or by an exact
current-tree citation. Every compiled witness has `autoImplicit`
disabled, contains no executable `sorry`/`admit`/custom `axiom`/`unsafe`
command, and has collected axioms within
`{propext, Classical.choice, Quot.sound}`. The planted bad witness retained
`sorryAx` and was rejected, calibrating the witness gate.

Evidence:

- [Tier-C register](review/recert_v6_tier_c.tsv)
- [Tier-C summary](review/recert_v6_tier_c_summary.txt)
- [seeded population](review/recert_v6_tier_c_seeded_population.tsv),
  [canonical frame](review/recert_v6_tier_c_seeded_frame.tsv),
  [selected sample](review/recert_v6_tier_c_seeded_sample.tsv), and
  [sampling summary](review/recert_v6_tier_c_seeded_sample_summary.txt)
- [seeded-sample build log](logs/recert_v6_tier_c_seeded_sample_build.log)
- [Tier-C command log](logs/recert_v6_tier_c_command.log)
- [Tier-C read-only validation](logs/recert_v6_tier_c_check.log)
- [planted-bad witness log](logs/recert_v6_tier_c_planted_bad.log)
- [Chapter 0–4 build](logs/recert_v6_tier_c_ch0_4_build.log),
  [Chapter 5–7 build](logs/recert_v6_tier_c_ch5_7_build.log), and
  [Chapter 8–9 build](logs/recert_v6_tier_c_ch8_9_build.log)

## Results

### Tier-A census

| Measure | Result |
|---|---:|
| Physical source files | 222 |
| Parsed declarations | 7,411 |
| Unparsed declarations | 0 |
| V4 type joins | 7,411 / 7,411 |
| Complete binder telescopes | 7,411 / 7,411 |
| Ambiguous or unmatched type joins | 0 |
| Auto-bound candidates | 0 |
| Red-flag hits | 13 |
| Reviewed false positives | 13 |
| SUSPECT / VACUOUS | 0 / 0 |

The 13 reason assignments were two contradictory-bound, two `Fin 0`, two
`IsEmpty`, four near-degenerate-bound, and three zero-`Fintype.card` hits.
Three reviewed false positives were escalated to Tier C and all three received
clean compiled witnesses.

### Removed conditional-interface scope

| Removed scope | Current V6 disposition |
|---|---|
| Equation (5.8) positive-Ricci conditional family | absent from source and Tier B |
| Exercise 8.39(a) and Remark 8.6.3 arbitrary-set upper Chevet forms | absent from source and Tier B |
| Example 3.4.6 Borell marginal tail specialization | absent from source and Tier B |

All six Tier-B ledgers are now entirely `OK`. The Chapter 8 supplement retains
Exercise 8.39(b) through its unconditional reverse-Chevet endpoint. The
Borell appendix module retains exactly the five normalized-law domain-support
declarations and no conditional marginal theorem.

## Re-run commands

Run from the project root:

```bash
python3 -B HighDimensionalProbability/Verification/scripts/test_v6_vacuity_scanner.py

python3 -B HighDimensionalProbability/Verification/scripts/v6_tier_a_scanner.py \
  --scope library \
  --v4-types-tsv HighDimensionalProbability/Verification/logs/recert_axiom_declaration_types.tsv \
  --v4-binders-tsv HighDimensionalProbability/Verification/logs/recert_axiom_declaration_binders.tsv \
  --format json \
  --output HighDimensionalProbability/Verification/logs/recert_v6_tier_a_final.json \
  --fail-on-unparsed \
  --require-complete-v4-join
python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_a_full_review.py
python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_a_full_review.py --check-only
```

```bash
python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_b_ch0_4.py --check
python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_b_supplement_ch0_4.py --check
python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_b_ch5_7.py --check
python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_b_supplement_ch5_7.py --check
python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_b_ch8_9.py --check
python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_b_supplement_ch8_9.py --check
python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_b_endpoints.py --self-test
python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_b_endpoints.py
```

```bash
python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_c_seeded_sample.py --write
python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_c_seeded_sample.py
python3 -B HighDimensionalProbability/Verification/scripts/recert_v6_tier_c.py --run
python3 -B HighDimensionalProbability/Verification/scripts/recert_v6_tier_c.py
python3 -B HighDimensionalProbability/Verification/scripts/check_v6_final.py --self-test
python3 -B HighDimensionalProbability/Verification/scripts/check_v6_final.py
```

The seeded builder's first command regenerates the population, canonical
frame, sample, and sampling summary; its second command is a read-only
reproducibility check. It fails if the active manifest is neither the semantic
baseline nor the exact successor authenticated through both the Round 10 and
Exercise-reorganization delta gates. The Tier-C
`--run` command rechecks those artifacts,
builds the three named witness modules, runs their axiom collectors, executes
the planted-bad calibration, and regenerates the 103-row register. The final
Tier-C command is a read-only exact-artifact check. The last two commands
calibrate and run the aggregate fail-closed V6 packet validator.

## Findings

| ID | Severity | Finding |
|---|---|---|
| None | None | No V6 finding. All 779 current Tier-B rows and all 103 Tier-C adjudication rows pass. |

## Limitations

1. Tier A is a lexical and telescope-based triage detector. Its silence alone
   is not semantic proof.
2. Tier B completely covers the fixed 702-row mandatory union, but does not
   claim a manual semantic read of every theorem in the environment. Exercise
   leaves are sampled at the required three per chapter.
3. Tier C covers 103 adjudication rows—50 retained fixed controls, 50 random
   controls selected by the frozen substantive-source seed, and three Tier-A
   escalations—not every one of the 7,411 parsed declarations. The stable seed
   is valid for the current digest only through the exact Round 10
   documentation-only and Exercise-reorganization delta gates cited above.
4. Citation and close-reading judgments are review-tier evidence. Their
   machine checks establish identity, coverage, source anchoring, and axiom
   cleanliness, not English mathematical intent.
5. Removed book scopes are not silently reclassified as current V6 successes;
   they are explicitly excluded from the active census and publication
   coverage statement.
