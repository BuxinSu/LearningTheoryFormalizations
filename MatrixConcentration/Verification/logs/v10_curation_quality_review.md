# V10 inline-curation independent quality review

Review date: 2026-07-20 (America/New_York)

## Result

The V10 inline curation is complete at the type-hash boundary checked here,
and the sampled semantic evidence supports its clean classifications. The
named-interface evidence also supports treating the three
NC-Khintchine/bootstrap interfaces as the single informational finding
V10-F1, rather than as an undisclosed assumption in a published result.
Book display (6.1.6) remains the sole declared formal-coverage exception;
the retained Rosenthal--Pinelis variants are nonregistered supporting results,
not substitute coverage endpoints.

No sampled row required escalation to
`DISCLOSED_CONDITIONAL_INFRASTRUCTURE`,
`UNDISCLOSED_CONDITIONAL_PRINCIPLE`, or `UNRESOLVED_REVIEW_RISK`.

The current `curation/README.md` agrees with the generated evidence: it labels
V10 as part of the post-correction V1–V10 re-certification, records all 368
persistent inline obligations, and states that the uncurated queue is empty.

## Scope and independence

This was a read-only quality audit of:

- `curation/v10_inline_adjudication.tsv`;
- `logs/v10_inline_review_obligations.tsv`;
- `logs/v10_inline_review_queue.tsv`;
- `logs/v10_inline_assumptions.tsv`;
- `logs/v10_inline_type_groups.tsv`;
- `logs/v10_summary.{txt,json}`;
- `logs/v10_status.tsv`, `logs/v10_consumers.tsv`, and
  `logs/v10_disclosure_reconciliation.tsv`;
- the cited source declarations and caller sites; and
- the V7/V10 witness-axiom records used to distinguish realizable model
  conditions from unavailable principles.

The review was read-only with respect to Lean source, both curation TSVs, and
the generated evidence. It did not launch Lean; this note records the review
of artifacts produced by the separate fresh V10 run. It does not use an
aggregate runner lifecycle marker as evidence.

The principal input digests were:

| Artifact | SHA-256 |
|---|---|
| `curation/v10_inline_adjudication.tsv` | `8f8d75096d31086991886a32a8ee2960c33c24a83e33b5821abe8c1658f31f1b` |
| `logs/v10_inline_review_obligations.tsv` | `b6156f630d452e51c754efab842868941697870ac6d856803ae0198cded35511` |
| `logs/v10_inline_review_queue.tsv` | `2399491456d28b3f694f8aa505dba10707337a3eace7a8bd5bf943854b976779` |
| `logs/v10_inline_assumptions.tsv` | `43b357efb5d2f05b72043e45cbce9860f0b43e8db7ba9e6d98395b8c319fab56` |
| `logs/v10_inline_type_groups.tsv` | `ead336e69c026609ef9cdc37fa86161a5ea2a719e9646eca8c820caf680fe3d2` |
| `logs/v10_summary.json` | `b1fd4659788b2e1bf86d7c264a3e992bdb2c4fbd72bbfa7eb1a5c3c3b3592f91` |
| `logs/v10_status.tsv` | `b44837175e3475879bd65d1e1bac88ef624053b1b3cdaa92c563d257eb5b1628` |
| `logs/v10_disclosure_reconciliation.tsv` | `f532e15925aa7d59584a342ea8c9a34b0d14ac6032727cde6368aa4016ad42f5` |

## Completeness and set-equality checks

The TSVs were parsed with Python's `csv.DictReader` using a tab delimiter.
For the four relevant sets, the following keys were compared:

```text
manual     = type_hashes of v10_inline_assumptions.tsv rows whose
             review_state is MANUALLY_ADJUDICATED
curated    = type_hashes in curation/v10_inline_adjudication.tsv
obligation = type_hashes in v10_inline_review_obligations.tsv
queue      = type_hashes in v10_inline_review_queue.tsv
```

The results were:

| Check | Result |
|---|---:|
| Curation rows / unique hashes | 368 / 368 |
| Obligation rows / unique hashes | 368 / 368 |
| Manual-review occurrences / unique hashes | 1,590 / 368 |
| `manual = curated` | yes |
| `manual = obligation` | yes |
| `curated = obligation` | yes |
| `queue` rows / hashes | 0 / 0 |
| Missing curation fields | 0 |
| Duplicate curation hashes | 0 |
| `ROUTINE_EXPLICIT_HYPOTHESIS` rows | 359 |
| `DISCHARGED_BY_SOURCE_CALLER` rows | 9 |

The queue file contained its header only. The curation and obligation files
each contained one header and 368 data rows.

Independent recomputation from `v10_inline_assumptions.tsv` gave:

| Occurrence category | Count |
|---|---:|
| `ANONYMOUS_INLINE_PREMISE` | 496 |
| `COMPOUND_PROJECT_PREDICATE_PREMISE` | 69 |
| `EXTERNAL_OR_LOCAL_NAMED_PREDICATE` | 1,025 |
| `INSTANCE_MEDIATED_PREMISE` | 584 |
| `NAMED_PROJECT_PREDICATE` | 129 |
| `PUBLISHED_ENDPOINT_INLINE_PREMISE` | 1,524 |
| **Total** | **3,827** |

The corresponding review-state counts were 1,590
`MANUALLY_ADJUDICATED`, 1,524
`COVERED_BY_V6_CORRESPONDENCE_REVIEW`, 584
`ENUMERATED_TYPECLASS_LIMITATION`, and 129
`RECONCILED_BY_CANDIDATE_CURATION`, again totaling 3,827. There were 542
stable normalized types overall.

As a separate coverage check, the 2,213 keys
`(module, name, kind)` in `v10_environment_constants.tsv` were compared with
the 2,213 corresponding keys in the independently generated
`axiom_audit.tsv`. Both sets had 2,213 unique keys, with zero V10-only and
zero V4-only keys.

## Sampling design

Forty-nine distinct curation rows were inspected. This was deliberately
stratified toward the shapes most capable of hiding an unavailable theorem:

1. all 9 `DISCHARGED_BY_SOURCE_CALLER` rows;
2. all 18 hashes whose type group includes
   `COMPOUND_PROJECT_PREDICATE_PREMISE`;
3. the 5 highest-occurrence anonymous-inline hashes, ordered by descending
   occurrence count and then ascending hash;
4. the 5 highest-occurrence external/local-headed hashes not already in
   strata 1–2, using the same ordering; and
5. 6 evenly spaced one-occurrence routine hashes from each of the anonymous
   and external/local pools.

For the one-occurrence strata, each pool was sorted by full hash and rows at
indices

```text
0, floor(n/5), floor(2n/5), floor(3n/5), floor(4n/5), n-1
```

were selected. The anonymous pool had 38 eligible rows and the external/local
pool had 106. All 49 selected hashes were distinct. The 12-hex prefixes below
uniquely identify rows in the 368-row curation (there were no 12-prefix
collisions).

### All caller-discharged rows

| Hash prefix | Occurrences | Declaration |
|---|---:|---|
| `5b51a9d86b9c` | 1 | `symmetric_small_dimension_algebra` |
| `5cccfebfdcb8` | 1 | `symmetric_small_dimension_algebra` |
| `83093392e01f` | 1 | `symmetric_large_dimension_algebra` |
| `889ea7aedf8c` | 1 | `sharp_khintchine_constant_is_sufficient` |
| `98894bb64e2d` | 1 | `sharp_khintchine_constant_is_sufficient` |
| `9992310ae96d` | 1 | `mul_le_of_le_mul_inv` |
| `a0518e3020e3` | 1 | `rosenthal_scalar_algebra` |
| `a44d2e5ad8bc` | 1 | `expectation_discrete` |
| `a5befe77b043` | 1 | `symmetric_large_dimension_algebra` |

### All compound-project-predicate rows

| Hash prefix | Occurrences | First declaration |
|---|---:|---|
| `08f7944502b6` | 5 | `expectation_sum_mul_conjTranspose_of_centered` |
| `19043f79163c` | 14 | `bernstein_cgf_trace_bound_one_sided` |
| `1e52547593d9` | 23 | `bernstein_cgf_trace_bound_one_sided` |
| `3472ed53e989` | 2 | `MIntegrable.finsetSum` |
| `3dff8367cc7a` | 5 | `sampleCov_norm_sum_sq_le` |
| `6911328b372a` | 3 | `conditional_column_bound` |
| `7e29bdddbc44` | 4 | `expectation_sum_mul_conjTranspose_of_centered` |
| `8aed64b609aa` | 4 | `entryDiag_sum_expectation` |
| `8bede019123b` | 10 | `bernoulliRepresentative_all_ae` |
| `abb0407d1a88` | 17 | `gauss_concentration` |
| `b5eef3e93ce1` | 7 | `matrix_rosenthal_pinelis_symmetric` |
| `bd5056b821ea` | 5 | `matrix_rosenthal_pinelis_symmetric_aux` |
| `df90a1e34daf` | 2 | `signed_expected_norm` |
| `e2e64dc5a80d` | 1 | `expectation_sum_mul_sum` |
| `e4a11e8e3cc4` | 1 | `integral_signFlip_eq_of_symmetric` |
| `e78c5d571866` | 5 | `er_compression_tail` |
| `e92aaa3896d0` | 2 | `symmetric_expect_sq_le_square_function` |
| `ee6bd27961e9` | 20 | `iIndepFun_rademacherRepresentative` |

### Highest-occurrence anonymous rows

| Hash prefix | Occurrences | First declaration |
|---|---:|---|
| `46d4edf30bb3` | 78 | `bernstein_cgf_trace_bound` |
| `8f5f137721af` | 78 | `bernstein_cgf_trace_bound` |
| `d3ee07766714` | 59 | `bernoulliRepresentative_all_ae` |
| `a009ba1f931b` | 49 | `bernstein_L_nonneg` |
| `e7b881f74a05` | 35 | `bernstein_cgf_trace_bound` |

### Highest-occurrence external/local-headed rows

| Hash prefix | Occurrences | First declaration |
|---|---:|---|
| `40acf93f23d8` | 160 | `bernsteinH_le_geom` |
| `9f90fbfe3ae7` | 127 | `add_smul_one_eq_cfc` |
| `66e9437c2b1e` | 118 | `bernstein_cgf_trace_bound` |
| `222d2ce4da5b` | 68 | `abs_eigenvalues_le_l2_opNorm` |
| `2ad59f9790ca` | 62 | `commute_posDef_inv` |

### Evenly spaced one-occurrence rows

| Category | Hash prefix | Declaration |
|---|---|---|
| Anonymous | `04ae8217dc57` | `column_family_bounds` |
| Anonymous | `315c0149f7e1` | `GaussPL.transfer` |
| Anonymous | `5bf0bf09531a` | `matrix_rosenthal_aux` |
| Anonymous | `a3b65c0744c8` | `conj_block_toBlocks₁₁` |
| Anonymous | `ca6a4beeb487` | `integral_log_le_log_integral` |
| Anonymous | `f378ed4b84a5` | `cfc_congr_of_eigenvalues` |
| External/local | `068c6098e4ef` | `Dyson.head_drop_eq_get` |
| External/local | `3acbce3a294e` | `weakVarianceSet_le` |
| External/local | `6ee07c53c01b` | `concaveOn_isOpen_expectation_le` |
| External/local | `9b395665344d` | private `mul_log_two_le_log_nat` |
| External/local | `dc42e34665d9` | `expectation_trace_exp_add_le'` |
| External/local | `ff97fb3d2e09` | `sampleCovariance_relative_error` |

For every sampled row, the adjudication, evidence, reviewer note, grouped
declaration list, occurrence count, first emitted occurrence, binder name,
domain head, and elaborated domain type were compared. The evidence was
specific to the premise or call site; no sampled row consisted merely of a
generic assertion that the premise was “routine.”

Across the complete 368-row curation, every evidence and reviewer-note field
was nonempty. Evidence lengths ranged from 36 to 136 characters and reviewer
notes from 29 to 186 characters. There were no duplicated evidence strings.

## Source-location and caller checks

A complete regex extraction of `*.lean:<line>` references from both evidence
columns found 51 citations. Each named source file existed and every cited
line was within the current file. Inspection of the resulting source-line
listing placed every citation in the named declaration or its associated
header/context.

The nine stronger caller-discharge claims were checked directly:

| Hash prefix | Premise | Source check |
|---|---|---|
| `5b51a9d86b9c` | low-dimensional `hy` | Derived from the proved centered-sum variance bound before calls at `Appendix_RosenthalPinelis.lean:2239` and `:3048`. |
| `5cccfebfdcb8` | low-dimensional coefficient `hc` | Derived from `small_dimension_min_le_variance_coefficient` before the same two calls. |
| `83093392e01f` | large-dimensional `hy` | Derived from `hlarge` / `symmetric_large_squared_bound_integrable` before calls at `:2249` and `:3059`. |
| `a5befe77b043` | large-dimensional coefficient `hc₁` | Both callers obtain it from `large_dimension_rosenthal_coefficients` and pass `hc'.1`. |
| `889ea7aedf8c` | sharp coefficient bound `hκ` | The sole call at `:632` passes the locally derived `hκsharp'`. |
| `98894bb64e2d` | exponent specialization `hr` | The same call passes `rfl`. |
| `9992310ae96d` | ENNReal inequality `h` | The sole call at `Appendix_GaussianConcentration.lean:942` passes locally proved `hinner`. |
| `a0518e3020e3` | Rosenthal scalar master inequality | The call at `Appendix_MatrixRosenthal.lean:1163` passes locally proved `hmaster`. |
| `a44d2e5ad8bc` | finite-index measurability `hV` | All nine source calls pass `measurable_id` or `measurable_of_countable`: seven in Chapter 6 (`:3467`, `:3913`, `:3927`, `:3983`, `:4441`, `:4698`, `:4707`) and two in Chapter 7 (`:3813`, `:3857`). |

These checks support the curation distinction between an ordinary explicit
input and a helper premise that the library's actual source callers prove
before use.

## Compound-premise analysis

The 69 compound-project-predicate occurrences formed 18 hashes. Their project
predicate dependencies were independently counted as:

| Dependency | Occurrences |
|---|---:|
| `MIntegrable` | 26 |
| `IsSymmetricRV` | 14 |
| `IsBernoulli` | 13 |
| `IsRademacher` | 12 |
| `IsStdGaussian` | 4 |

There were zero compound occurrences involving
`HermitianNCKhintchineAt`, `RectangularNCKhintchineAt`, or
`ProvidesCenteredRosenthalBootstrap`. Direct binders for those three
predicates were routed to the named-interface census instead of being hidden
inside the inline curation.

Review of all 18 compound rows found explicit finite-family integrability,
symmetry, or probability-law conditions. Their evidence names the quantified
family and the declarations in which it occurs. Nothing in this stratum
packaged an NC-Khintchine or centered-bootstrap conclusion.

## V10-F1 analysis

The named-interface evidence supports the report's V10-F1 classification.

The source banner at `Appendix_RosenthalPinelis.lean:342–345` states that the
section is conditional-only, supplies no witness for either Khintchine
predicate, and proves the retained Rosenthal--Pinelis supporting results
separately. The file-level disclosure and project records explicitly exclude
(6.1.6) from formal coverage. The retained variants are not correspondence
endpoints.
The three relevant proposition definitions are:

- `HermitianNCKhintchineAt` at line 352;
- `RectangularNCKhintchineAt` at line 366; and
- `ProvidesCenteredRosenthalBootstrap` at line 478.

The fixed-point status data show:

| Predicate | Source status | Producer candidates | Consumers |
|---|---|---:|---:|
| `HermitianNCKhintchineAt` | `CONSUMED-ONLY` | 0 | 1 |
| `RectangularNCKhintchineAt` | `CONSUMED-ONLY` | 1 | 3 |
| `ProvidesCenteredRosenthalBootstrap` | `CONSUMED-ONLY` | 0 | 2 |

The one rectangular producer candidate is
`hermitian_nckhintchine_implies_rectangular`; it depends on the still-unproved
Hermitian predicate and therefore does not enter the least fixed point.

`v10_consumers.tsv` records only four distinct conditional roles:

1. `hermitian_nckhintchine_implies_rectangular`;
2. the definition-body dependency in
   `ProvidesCenteredRosenthalBootstrap`;
3. `matrix_rosenthal_pinelis_of_nck_and_bootstrap`; and
4. `matrix_rosenthal_pinelis_of_sharp_nck_and_bootstrap`.

Every one is marked absent from the 467-row correspondence table. Direct
search of `v6_correspondence_rows.tsv` and the source README correspondence
register found none of those conditional roles or three interface names. The
README explicitly names (6.1.6) as the sole coverage exception and treats the
retained symmetric, centered-with-loss, and integrable `_aux` declarations as
nonregistered supporting results.

The disclosure reconciliation is also bidirectional:

- `TranslationReport/SOURCE_STATEMENT_ISSUES.md` states that the literal
  centered exact display needs sharp NC-Khintchine/centered-bootstrap input
  for which no witness is present, and that the conditional predicates do not
  assert the claim.
- `APPENDIX_SUMMARY.md` labels the literal centered exact display
  as excluded from formal coverage and labels related symmetric and
  centered-with-loss variants as supporting results rather than
  correspondence endpoints.
- `v10_disclosure_reconciliation.tsv` maps all three detected interfaces to
  that disclosure, reports zero correspondence consumers for them, and
  records `INFO:V10-F1`.

The remaining source-level `CONSUMED-ONLY` predicates are qualitatively
different. `IsStdGaussian`, `IsBernoulli`, and
`HasReproducingProperty` are explicit probability/model conditions.
`v7_witness_axioms.tsv` and `v10_witness_axioms.tsv` record compiled concrete
models for them using only `propext`, `Classical.choice`, and `Quot.sound`.
Those witnesses establish realizability without relabeling the predicates as
source-produced.

Together, these facts support the following limited conclusion: the three
NC-Khintchine/bootstrap interfaces are real, never-unconditionally-produced
principles, but they are explicitly disclosed and confined to unpublished
conditional reductions. Treating them as one INFO finding is supported; the
audited inventories contain no evidence that a result presented as
established relies on them.

## Limitations

- The machine checks establish completeness and exact set reconciliation, not
  the correctness of a human semantic label. This review independently
  inspected 49 of 368 curation rows, deliberately weighted toward risky
  shapes; it was not a second full semantic adjudication of all 368.
- The 51-citation range check proves that references resolve into the current
  source and the manual caller checks establish the nine claimed discharges.
  A valid line reference alone is not a proof of a semantic judgment.
- The inline inventory covers proposition-valued binders on source-backed
  imported theorems. It is not unrestricted semantic theorem discovery in
  arbitrary proof bodies or non-propositional encodings.
- The instance inventory records 4,762 theorem instance binders, 22 heads,
  and 584 proposition binders routed to the explicit typeclass limitation.
  It does not prove global instance availability for every imported Mathlib
  type or future downstream declaration.
- Concrete model witnesses establish consistency and realizability. They do
  not prove source-level producer status or re-audit book-faithfulness.
- This note did not rerun the Lean environment emitters. It relies on the
  hash-identified generated artifacts and independently recomputes their
  relevant row sets, counts, and cross-file identities.
