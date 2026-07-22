# V10 — Conditional-interface and undischarged-assumption census

**Verdict: PASS-WITH-NOTES**

V10 found no undisclosed published result that depends on a project-owned
condition the repository never supplies.  The fresh whole-environment census,
the independent source scan, the V4/V6/V7 joins, and both exact review closures
all pass.  The only finding is informational: ten source-disclosed conditional
infrastructure items have unpublished consumers only.

This report has 0 CRITICAL, 0 MAJOR, 0 MINOR, and 1 INFO finding.

## Scope and question

V10 asks a narrower question than “does this theorem have hypotheses?”  Lean
theorems normally have mathematical hypotheses.  The audit instead asks
whether a published result rests on a project-owned principle, certificate, or
interface that is consumed but never constructed, and whether any such
conditionality is accurately disclosed.

This failure mode is structurally invisible to V3 and V4. A theorem of type
`P → Q` remains sorry-free and axiom-clean even when the project never proves
the project-owned premise `P`; only a producer/consumer census can distinguish
an ordinary mathematical hypothesis from an undisclosed assumed principle.

The checked physical surface is 222 Lean files: 212 below
`HighDimensionalProbability/` and all 10 `MatrixConcentration/` modules.  With
the separate `HighDimensionalProbability.lean` root, the environment census
covers exactly 223 modules.  The run is bound to source-manifest digest
`78da8753a3367be0ae4c72df049a99f33723a7b22a1d08384714cc59d08853d4`.

The environment harness imports the HDP root, the isolated Appendix closure,
and every MatrixConcentration module.  It enumerates:

- Prop-valued definitions and abbreviations;
- structures and classes with Prop-valued fields, plus those fields;
- binder, conclusion, witness, and definition-body references to each named
  candidate; and
- every Prop-valued binder of every project theorem, including unnamed inline
  hypotheses.

An independent masked source scan covers every physical file, including files
that could otherwise be missed by an import-based check.  The analyzer then
joins the result to all 15,022 fresh V4 declarations, the 519-theorem V6
Tier-B endpoint union, the fresh V7 constants and dead-code evidence, and the
live documentation claims.

## Method and fail-closed controls

Named candidates are classified by a least-fixed-point analysis:

- `PROVED` means a declaration supplies the proposition/interface and every
  project-candidate prerequisite of that producer is itself discharged;
- `CONSUMED-ONLY` means there is a real consumer but no discharged producer;
  these rows require exact review rather than being treated automatically as
  defects; and
- `DEAD` means V10 found neither a producer nor a binder consumer, so the row
  is reconciled with V7 instead of being silently ignored.

The least-fixed-point rule prevents a cycle such as `P` from `Q` and `Q` from
`P` from certifying itself.  The self-test also checks a planted consumed-only
principle, exact-population acceptance, count/key/raw-type drift rejection,
raw Lean-expression parsing, removed-family absence, the 15-row Appendix
witness, and controlled rejection of missing evidence.

The review is fail-closed at two levels:

1. all 250 consumed-only primary candidates are bound to exact consumer and
   type identities; and
2. 2,911 structurally selected inline binders are bound to exact key and raw
   kernel-type identities.

During the fresh recertification, the first analysis intentionally rejected
the pre-removal expected counts and digests.  The observed deletion-only
populations were reviewed, the constants were refreshed to those measured
digests, and the final analysis and exact-currentness check both passed.  The
final review bindings are:

| Review population | Rows | Current digest |
|---|---:|---|
| Primary consumed-only key/type population | 250 | `196bb94c3ebe325d337a19f6523c176fb294c05af9f603000c8ee2ed6797d3cb` |
| Inline exact-review keys | 2,911 | `17366877da50fa50fe0ead802163a479e2a912cf8583f7ae2b35abd171e4c1c9` |
| Inline exact-review raw types | 2,911 | `c376a0c15a2da9f530128dac906b468291c27e5328b24dfbbe7b698600d41176` |

The [exact review closure](logs/v10_review_closure.txt) records equal observed
and expected digests and no closure error.  This refresh is not a blanket
acceptance of drift: any future row, identity, publication flag, or raw type
change again makes V10 incomplete until it is reviewed.

## Fresh census

| Surface | Current result |
|---|---:|
| Physical source files | 222 = 212 HDP + 10 MatrixConcentration |
| Environment modules | 223/223 |
| Fresh V4 declarations joined | 15,022 |
| Fresh V6 Tier-B theorem endpoints joined | 519 |
| Explicit textual Prop definitions | 161 = 152 HDP + 9 MatrixConcentration |
| Primary environment candidates | 352 = 319 predicates + 33 interfaces |
| Prop-valued structure/class fields | 138 |
| Primary statuses | 86 proved / 250 consumed-only / 16 dead |
| Inherited field statuses | 52 proved / 86 consumed-only / 0 dead |
| Candidate-reference consumer rows | 3,616 |
| All theorem Prop binders | 15,381 |
| Mixed-tier inline review rows | 4,734 |
| Published or documentation-claimed inline rows | 2,279 |
| Unpublished risk/override inline rows | 2,455 |
| Exact digest-bound inline review rows | 2,911 |
| V6-reconciled primary / inline targets | 84 / 168 |

The 319 environment predicates contain all 161 explicit textual definitions;
158 additional predicates are environment-only because their result is
inferred or reducible, compiler-generated, private-mangled, or not written
with a literal `: Prop`.  There are zero text-only predicates and zero
ambiguous textual matches.

The broader 4,734-row inline inventory contains named-candidate, ordinary
local/typeclass, exact structural-review, and explicit override rows.  Within
it, the 2,911-row exact structural population partitions into 2,200
root-universal rows and 711 nested-Pi-or-non-forall rows.  The exact structural
clusters are:

| Cluster | All rows | Published or claimed |
|---|---:|---:|
| Nested Pi or non-forall | 711 | 55 |
| Relation/logic | 1,123 | 198 |
| Analytic regularity | 770 | 166 |
| Probability law | 128 | 26 |
| Matrix structure | 126 | 7 |
| Set/geometric | 48 | 5 |
| Local predicate | 5 | 0 |
| **Total** | **2,911** | **457** |

These structural groups classify raw binder shapes.  A row may receive a
stronger final adjudication—for example, a locally discharged certificate—so
the group labels and the final adjudication labels serve different purposes.

## Removed interfaces and retained finite statements

The [16-row removal reconciliation](review/v10_ledger_reconciliation.tsv)
confirms exact absence from source, V4, V7, V6, and all V10 candidate,
reference, and inline surfaces for 12 declarations:

- `HDP.Chapter3.BorellConvexBodyPsiOnePrinciple` and
  `HDP.Chapter3.convexBodyUniform_marginal_subExponential_of_borell`;
- `HDP.Chapter5.positive_ricci_concentration`,
  `HDP.Chapter5.positive_ricci_concentration_psi2`, and
  `HDP.Chapter5.positive_ricci_concentration_psi2_of_lipschitz`; and
- `HDP.Chapter8.GaussianChevetUpperPrinciple`,
  `HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary_envelope`,
  `HDP.Chapter8.gaussianChevetExpectationEnvelope_ne_top_of_isBounded`,
  `HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary_envelope`,
  `HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary`,
  `HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary`, and
  `HDP.Chapter8.gaussianChevetUpperPrinciple_external`.

It also confirms physical absence of
`HighDimensionalProbability/Appendix/GaussianChevet.lean` and
`HighDimensionalProbability/Appendix/PositiveRicciConcentration.lean`.

The original pre-removal V10 contract named
`HDP.Chapter5.positive_ricci_concentration` as its required live calibration
positive. The later final-correction decision deliberately removed that
interface and superseded the calibration obligation: on the active snapshot,
exact absence of the former positive is mandatory, while the planted
consumed-only fixture remains the live detector calibration. Treating the
deleted declaration as a required current positive would contradict the
accepted source-removal boundary.

The deletion did not hide the finite theorem signatures.  Both
`HDP.Chapter8.exercise_8_39a_gaussian_chevet` and
`HDP.Chapter8.remark_8_6_3_gaussian_chevet` remain present with an explicit,
source-visible `hzero : 0 ∈ T`; the source/environment/override join is 2/2
PASS.  The 15 retained Appendix/V6 axiom replays also compile against the
current Appendix.

`HDP.Appendix.RiemannianDiffusionLaw` remains as reviewed, direct,
data-bearing unpublished infrastructure.  Its four exact consumers are the
three corresponding infrastructure consequences and
`HDP.Chapter5.special_orthogonal_concentration_of_diffusion`; none is a Tier-B
published completion.  The separate headline Special Orthogonal theorem uses
an independently discharged route.

## Published-surface and V7 reconciliation

Every ordinary V10 target on the published surface is joined back to the
current V6 review:

- 84 primary-candidate Tier-B consumers; and
- 168 inline-binder Tier-B declarations.

Every one has the expected V6 status `OK`.  The exact join is recorded in
[v10_v6_review_reconciliation.tsv](review/v10_v6_review_reconciliation.tsv).
No informational item below has a Tier-B consumer.

All 16 V10 `DEAD` candidates are present in the fresh V7 environment.  Six are
confirmed V7 dead-code candidates, six have live implementation-level reverse
references, and four Exercise declarations are excluded by V7's documented
rules.  Thus `DEAD` is a V10 interface-use classification, not an automatic
deletion recommendation.  See
[v10_v7_dead_reconciliation.tsv](review/v10_v7_dead_reconciliation.tsv).

## Exact V10-F1 informational items

The exact ten-item set is:

1. `HDP.Appendix.BochnerRicciCertificate`
2. `HDP.Appendix.HasExponentialEnergyBound`
3. `HDP.Appendix.HasGammaTwoLowerBound`
4. `HDP.Appendix.HasHerbstEntropyBound`
5. `HDP.Appendix.HasUniformPositiveBounds`
6. `HDP.Appendix.MarkovSemigroupData`
7. `HDP.Appendix.MarkovSemigroupData.GammaTwoFlowCertificate`
8. `HDP.Chapter5.special_orthogonal_concentration_of_diffusion[0:hDiffusion]`
9. `LogSobolev.dualEntropySet`
10. `LogSobolev.dualEntropySetT`

The nine named primary items are source-disclosed certificate-bearing or
auxiliary infrastructure with unpublished consumers only.  The eighth is the
explicit `hDiffusion` binder of an unpublished exact-reduction helper.  Its
source documentation identifies heat-diffusion construction as the premise,
while the published Special Orthogonal endpoint follows the separate ambient
log-Sobolev route.  The exact rows, consumers, source anchors, and rationales
are in [v10_adjudication.tsv](review/v10_adjudication.tsv),
[v10_primary_review_closure.tsv](review/v10_primary_review_closure.tsv), and
[v10_inline_review_closure.tsv](review/v10_inline_review_closure.tsv).

## Calibration and command results

| Gate | Result | Evidence |
|---|---|---|
| Self-test, including drift and missing-evidence rejection | PASS | [self-test](logs/v10_self_test.log) |
| Complete source preview; removed names/files absent; finite signatures 2/2 | PASS | [source preview](logs/v10_source_preview.log) |
| Planted consumed-only conditional theorem compiles and is detected | PASS | [planted build](logs/v10_planted_build.log); [calibration](logs/v10_calibration.tsv) |
| Former named positive after the final-correction scope decision | SUPERSEDED BY REMOVAL; exact source/environment absence required and confirmed | [removal reconciliation](review/v10_ledger_reconciliation.tsv); [historical projection](inventory/pass07_census_projection.tsv) |
| Complete 223-module environment harness | PASS, exit 0 | [harness build](logs/v10_harness_build.log) |
| Current 15-row Appendix axiom witness | PASS, exit 0 | [witness build](logs/v10_pass07_appendix_axioms_build.log) |
| Removed-interface and retained-finite reconciliation | PASS | [ledger reconciliation](review/v10_ledger_reconciliation.tsv) |
| Exact primary and inline review closure | PASS | [review closure](logs/v10_review_closure.txt) |
| Final analysis | PASS-WITH-NOTES; ten INFO items grouped as V10-F1, with no CRITICAL, MAJOR, or MINOR findings | [summary](logs/v10_summary.txt) |
| Exact-currentness replay | PASS | [check](logs/v10_check.log) |

The complete generated inventories are
[v10_textual_predicates.tsv](inventory/v10_textual_predicates.tsv),
[v10_environment_predicates.tsv](inventory/v10_environment_predicates.tsv),
[v10_environment_text_diff.tsv](inventory/v10_environment_text_diff.tsv),
[v10_predicate_census.tsv](inventory/v10_predicate_census.tsv),
[v10_consumers.tsv](inventory/v10_consumers.tsv), and
[v10_inline_hypotheses.tsv](inventory/v10_inline_hypotheses.tsv).

## Exact re-run commands

Run from the project root after the current V4, V6, and V7 artifacts exist:

```text
python3 -B HighDimensionalProbability/Verification/scripts/v10_conditional_interfaces.py self-test

python3 -B HighDimensionalProbability/Verification/scripts/v10_conditional_interfaces.py source-preview

python3 -B HighDimensionalProbability/Verification/scripts/v10_conditional_interfaces.py run

python3 -B HighDimensionalProbability/Verification/scripts/v10_conditional_interfaces.py analyze

python3 -B HighDimensionalProbability/Verification/scripts/v10_conditional_interfaces.py check
```

The `run` mode records and executes the planted fixture, the complete
environment harness, and the 15-row current Appendix witness.  The precise
nested Lean commands and working directory are preserved in
[v10_command.log](logs/v10_command.log).  `analyze` regenerates every V10
inventory and review artifact; `check` recomputes them without accepting
drift and requires the final issue set to contain no CRITICAL or MAJOR item.

## Findings

| ID | Severity | Finding | Evidence |
|---|---|---|---|
| V10-F1 | INFO | Ten source-disclosed conditional infrastructure items have unpublished consumers only.  No Tier-B result depends on them, and the published Special Orthogonal theorem uses a separately discharged route. | [exact item list](logs/v10_summary.txt); [adjudication](review/v10_adjudication.tsv); [primary closure](review/v10_primary_review_closure.tsv); [inline closure](review/v10_inline_review_closure.tsv); [V6 reconciliation](review/v10_v6_review_reconciliation.tsv) |

## Limitations

- V10 detects project-owned conditional interfaces and exact theorem Prop
  binders; it does not declare an ordinary measurability, boundedness,
  integrability, typeclass, or data-bearing hypothesis defective merely
  because it is a hypothesis.
- V10 detects never-discharged named assumptions; it does not decide whether a
  discharged assumption's proof is itself mathematically meaningful. That
  semantic question belongs to V6's vacuity and witness review.
- Typeclass-mediated conditionality was audited through Prop-valued
  structure/class fields, the instance inventory joined from V5, and every
  theorem Prop binder. The census does not claim that every possible
  data-bearing typeclass has a canonical project instance.
- The exact review closures bind the current population and raw types.  They
  make later drift visible but do not replace mathematical judgment about a
  newly introduced interface.
- The 16 `DEAD` rows are cross-file V7 triage results, not a deletion list.
- V10 does not solve the separately ledgered Exercise `sorry` leaves or
  re-audit the Lean kernel and pinned dependencies; those scopes belong to
  V3/V4 and the project trust boundary.
- Removed arbitrary-set Chevet, equation-(5.8), and Borell interfaces are not
  represented as live conditional theorems.  Their exclusion from the active
  publication scope is documented in the correction and faithfulness records;
  V10 certifies their exact absence and the retained finite signatures.
