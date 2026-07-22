# V7 load-bearing definition review protocol

This is the manual-review contract for the complete row set emitted by
`scripts/definition_sanity.py`. It is deliberately separate from the machine
candidate inventory. The current fail-closed review contract version is `2`.

## Non-negotiable distinction

`definition_nontriviality_candidates.tsv` is a search aid. A row there means
only that a theorem statement directly mentions a load-bearing definition.
It does **not** mean that the theorem proves the definition nonconstant,
nondegenerate, or faithful on its intended domain.

A reviewer may promote a candidate to `VERIFIED_CITATION` only after recording:

1. the concrete nondegenerate model or input class;
2. the exact substantive property forced by the cited theorem;
3. why that property would fail under the relevant zero/constant/hollow
   interpretation;
4. the `sInf`/`sSup`, division, empty-index, measure, sigma-algebra, and
   typeclass boundary checks relevant to the definition; and
5. the citation's V4 axiom result and source location.

The validator rejects a promoted citation lacking any of these fields.
Use `(none)` in `evidence_axioms` when V4 reports the empty axiom set; leaving
the field blank means the review is incomplete. The recorded source location
must be the packet's canonical physical source declaration. For a direct
theorem, lemma, alias, or named instance this is in the candidate's measured
project module. For a compiler-generated constant it is the uniquely verified
owning declaration described below, which can precede the module that
materialized the generated constant.

## Static packet source-owner rules

`v7_review_packet.py` labels every source resolution mode and fails closed on
missing or ambiguous owners. It permits only these auditable cases:

- a direct exact/private theorem, lemma, alias, definition, structure, class,
  or named-instance declaration;
- a finite compiler suffix (`eq_N`, `congr_simp`, `_proof_*`, `_simp_*`, or
  `_abel_*`) attached to the unique longest physical source owner;
- a structure/class field or constructor helper whose exact V4 type contains
  that owner;
- a cross-module `eq_N` or `congr_simp` only when the stripped owner occurs in
  the candidate's exact V4 type, has an exact V4 row, and has one physical
  source declaration; or
- a compiler-named anonymous instance only when its normalized source type and
  exact V4 type identify one complete source/V4 ordinal group. Repeated
  anonymous instances are bound in lexical source order to the unsuffixed,
  `_1`, ... V4 names.

V4 reports Lean structures and classes as `inductive`. The packet normalizes
that kind only when the shard says `structure` or `class` and the exact
same-name physical declaration has that exact source keyword. A wrong owner,
wrong kind, unsupported name shape, incomplete ordinal group, or ambiguous
physical anchor is a packet failure, never a heuristic fallback.

## Allowed final dispositions

- `VERIFIED_CITATION`: human semantic review plus a V4-clean theorem-statement
  candidate.
- `VERIFIED_WITNESS`: a fresh named concrete witness with `autoImplicit false`,
  no executable `sorry`/`admit`/`sorryAx`, build exit zero, a type that directly
  mentions the audited definition, and axioms contained in
  `{propext, Classical.choice, Quot.sound}`. The witness source must be a
  physical file under
  `HighDimensionalProbability/Verification/scripts/witnesses/`; its collector
  source must be a physical file under `.audit_work/verification/`. Its
  recorded location must point to the exact named theorem/lemma declaration,
  not merely an in-range line in the same file.
- `UNVERIFIED_SANITY`: no acceptable citation or witness; the row names a
  `V7-Fn` finding, severity, blocker, and what remains to be checked.

`UNREVIEWED` is valid only while work is in progress. Final validation rejects
every remaining `UNREVIEWED` row.

## Reproducible partition

After `definition_sanity.py` has produced its final TSV inputs, run:

```text
python3 HighDimensionalProbability/Verification/scripts/v7_definition_review.py prepare
```

The script keeps each Lean module in one shard and greedily balances module
groups across four shards. The manifest and stable SHA-256-based review IDs
prove that the shards form an exact, duplicate-free partition of the complete
load-bearing set.

Validate work in progress with:

```text
python3 HighDimensionalProbability/Verification/scripts/v7_definition_review.py validate
```

The final gate is:

```text
python3 HighDimensionalProbability/Verification/scripts/v7_definition_review.py validate --final
```

The final gate checks the load-bearing union, candidate inventory, manifest,
all shard metadata, reviewer dispositions, V4 citation axioms, and independent
compiled-witness evidence. It never promotes a candidate automatically.

## Objective compiled-witness evidence contract

`definition_witness_evidence.tsv` contains only identities and physical
evidence pointers:

```text
definition  witness  witness_module  source_path  build_log  collector_source  collector_log
```

It contains no reviewer-authored `source_clean`, `build_exit_code`, axiom, or
type-dependency booleans. The validator derives those facts independently:

1. `build_log` must be a `run_logged.py`-style log for an exact
   `lake env lean <source_path>` invocation, with exactly one `exit_code: 0`
   footer as its terminal nonempty line and no error, sorry, admit, or
   `sorryAx` diagnostic.
2. The lexer-masked witness source must contain executable
   `set_option autoImplicit false`, must contain no executable
   `sorry`/`admit`/`sorryAx`, and must have exactly one resolvable theorem or
   lemma matching the named witness at `evidence_location`.
3. `collector_log` must similarly be a completed exact
   `lake env lean <collector_source>` log. Its collector source must use both
   `collectAxioms` and theorem-type `getUsedConstants`, and must import the
   canonical module obtained from the witness source path. The evidence row's
   `witness_module` must equal that canonical source module.
4. The collector prints exactly one tab-separated row:

```text
V7_WITNESS_COLLECTOR  module  name  kind  private_user_name  axioms  type_dependencies
```

   Here `kind` must be `theorem`, `name` and `module` must match the evidence
   row, `type_dependencies` must directly contain the audited definition, and
   `axioms` must exactly match the review row and be a subset of the allowed
   three. Empty axiom/private-name fields remain empty between tab separators.

Any missing, duplicated, hand-asserted, nonterminal, mis-anchored, or
source/log-mismatched evidence fails validation. If no such compiled evidence
has actually been generated, use `UNVERIFIED_SANITY`; never manufacture a
`VERIFIED_WITNESS` row.

## Partition and finding invariants

Every review row must physically remain in the shard file named by its
machine-owned `shard` field, and every module remains wholly in one physical
shard. Reusing one `V7-Fn` across several `UNVERIFIED_SANITY` rows is allowed
only when its severity and blocker text are identical. Final validation also
rejects stale finding fields on verified rows and stale evidence/semantic
claim fields on unverified rows.
