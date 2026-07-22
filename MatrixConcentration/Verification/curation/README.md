# Review-tier curation contracts

## V6 Tier B

The eight `v6_tier_b_chapter_N.tsv` files are the human-review source of truth.
They are not generated verdicts. Each reviewer owns disjoint chapter files and
must read the exact endpoint telescope and source declaration before filling a
row.

The fixed columns are:

1. `global_row`, `chapter`, `chapter_row`, `readme_line`, `book_source`,
   `declaration`, `endpoint_kind`: immutable metadata. These must match the
   README extraction and compiled environment exactly.
2. `verdict`: exactly `OK`, `SUSPECT`, or `VACUOUS`.
3. `check1_model`: a declaration-specific jointly satisfiable nondegenerate
   model, including concrete values for substantive scalar side conditions.
4. `check2_nontrivial`: why the endpoint is not independently discharged by a
   junk convention; if a boundary does collapse, describe it and use
   `SUSPECT`.
5. `check3_typeclasses`: why the exact typeclasses/measure/matrix structures
   admit the intended model, including empty-dimension issues.
6. `check4_quantifiers`: whether the exact telescope is usable, with attention
   to guards, existential weakening, and auto-bound identifiers.
7. `adjudication`: a row-specific conclusion that names the declaration and
   explains the verdict.
8. `evidence_refs`: source location plus concrete theorem/witness/application
   references supporting the judgment.

Do not copy a generic paragraph across endpoints. The merger rejects the
legacy generated phrases, blank/short checklist cells, missing declaration
names, metadata drift, and duplicate rationales. A SUSPECT/VACUOUS verdict is
an evidence obligation and must be covered by Tier C before V6 can pass.

## V10 named and inline assumptions

V10 is part of the post-correction V1–V10 re-certification. Its review
register contains all 368 persistent inline type-hash obligations, the
uncurated queue is empty, and the post-review census records zero errors and
`VERDICT PASS`. The semantic classifications remain review-tier judgments:
the runner validates their completeness, source coordinates, controlled
labels, and reconciliation with the machine census; it does not manufacture
those judgments automatically.

`v10_adjudication.tsv` is the complete review register for the 14
proposition-valued `def`/`abbrev` declarations found independently by the
environment and textual censuses. Its predicate names and statuses must match
the generated census exactly; the production checker rejects missing, extra,
duplicate, stale, or blank rows.

`v10_inline_adjudication.tsv` is the complete review register for the stable
type hashes left after project predicates, the 467 V6-reviewed published
endpoints, and explicitly limited instance binders have been separated from
the exhaustive theorem proposition-binder inventory. A nonempty external or
local proposition head is not an automatic exemption: equalities,
inequalities, measurability conditions, and similar headed formulae enter this
register when they occur outside the V6 row set, because their shape alone
cannot prove that they are routine. Likewise, only a direct application of a
curated project predicate is reconciled automatically; a compound premise
that merely mentions one is reviewed here so that an additional conjunct or
antecedent cannot hide behind the named-predicate classification.
Its fixed columns are:

1. `type_hash`: the stable alpha-normalized SHA-256 emitted in the generated
   review queue;
2. `adjudication`: the controlled review classification;
3. `evidence`: a source-specific declaration, binder, or discharge reference;
4. `reviewer_note`: the reason the row is or is not a never-discharged
   principle.

Clean rows use `ROUTINE_EXPLICIT_HYPOTHESIS` or
`DISCHARGED_BY_SOURCE_CALLER`. The checker recognizes
`DISCLOSED_CONDITIONAL_INFRASTRUCTURE`,
`UNDISCLOSED_CONDITIONAL_PRINCIPLE`, and `UNRESOLVED_REVIEW_RISK` only as
fail-closed finding states: recording any one prevents a machine PASS until
the report and disposition are updated.

The V10 checker requires every applicable curation hash to be used and every
generated obligation to be discharged, rejects duplicate, stale, blank, or
placeholder evidence, and fails if any review-queue hash has no curated
disposition. The generated obligations and queue retain deterministic hash
order. Generated row-level results remain under `logs/`; these two curated
files record the non-push-button judgments.

For the recertification expansion, the deterministic queue is split into
three equal ordered review chunks under `.audit_work/`. After all three
reviewers have inspected every occurrence of their assigned hashes,
`scripts/v10_merge_inline_reviews.py` checks each chunk's exact ordered hash
set, controlled labels, evidence quality, duplicates, and the set equation

`existing curation ∪ reviewed queue = persistent review obligations`.

Run it without arguments for validation and with `--apply` for an atomic,
hash-sorted replacement of `v10_inline_adjudication.tsv`. The subsequent
`v10_census.py` run remains authoritative: any finding-state adjudication or
unused/missing hash forces V10 to fail.
