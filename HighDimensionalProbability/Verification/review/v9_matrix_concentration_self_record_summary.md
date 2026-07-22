# V9 MatrixConcentration self-record audit

This is a deterministic static reconciliation of the five live self-record documents against V1–V5 evidence. It does not invoke Lean or Lake.

- Ledger: `HighDimensionalProbability/Verification/review/v9_matrix_concentration_self_record.tsv`
- Script: `HighDimensionalProbability/Verification/scripts/v9_matrix_concentration_self_record.py`
- TSV SHA-256: `a568b2c67d33bb84789930d44482394897a577ce724260c882d9d8af8ced58f7`
- V4 raw state: `COMPLETE` (15052 readable rows; 1508 MC-origin rows)

## Result

- Claims audited: **632**
- Verdicts: `CONTRADICTED=11`, `MATCH=384`, `OVERSTATED=162`, `PENDING=30`, `STALE=26`, `UNVERIFIABLE=19`
- Major/critical stale, overstated, or contradicted claims: **186**

The decisive result is that the documents conflate two different facts: all 448 README mappings are source-located, but the complete 14-file MatrixConcentration surface is not currently elaboratable. `Appendix_RosenthalPinelis` has nine direct errors, and its failure blocks Chapters 1, 6, and 7. The compatibility root succeeds because it imports only Chapter 2.

## README correspondence

- Physical rows: **448** (asserted declarations: **447**; explicit non-theorem: **1**).
- Asserted rows in the ten buildable modules: **309**.
- Asserted rows in the four failed/dependency-blocked modules: **138**.
- Per-row current verdicts: `MATCH=310`, `OVERSTATED=138`

Every asserted row has a declaration header of the claimed kind in the claimed source file. That proves lexical source location, not book faithfulness. Rows in failed modules are explicitly `OVERSTATED`, never silently counted as kernel-verified. The completed V4 dump contains an exact module-and-name row for every asserted README mapping in a buildable module; no such README row remains `PENDING`.

## Principal contradictions and stale records

- `MatrixConcentration_audit.md` says 14/14 files compile with zero errors; V1 proves four failures and nine direct errors.
- The same audit says the review notes have 16 rows in one place, while the live file has 15 source-gap rows plus 5 merge rows (and the audit itself later says 15 + 5).
- `APPENDIX_SUMMARY.md` describes a current `Appendix/01_...` through `11_...` layout. That directory and all eleven files are absent after the five-file merge.
- `APPENDIX_SUMMARY.md` says the root imports Appendix 01–11; the current root imports only `MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices`.
- Placeholder freedom is real at source level: all 14 MC source files have zero executable `sorry`, `admit`, `native_decide`, or custom-axiom declarations. This does not repair elaboration errors.

## Headline axiom claims

The audit's 17-name exact-axiom list crosses the build boundary. Nine headline declarations are sourced in buildable modules and eight are in Ch1/Ch6/Ch7. Only exact module-and-name V4 rows are accepted; a duplicate qualified name originating in another HDP module cannot authenticate a failed MatrixConcentration source module.

## Review-notes status

All explicit declaration-location references in `REVIEW_NOTES.md` are checked individually. Semantic claims about correspondence to Tropp, almost-everywhere versus pointwise assumptions, or body preservation remain `UNVERIFIABLE` unless V1–V5 contains the required comparison artifact. References in failed modules are source-present but `PENDING` kernel/build confirmation.

## Document row counts

- `Pre_MatrixConcentration/APPENDIX_SUMMARY.md`: 27
- `Pre_MatrixConcentration/MatrixConcentration_audit.md`: 46
- `Pre_MatrixConcentration/README.md`: 474
- `Pre_MatrixConcentration/REVIEW_NOTES.md`: 81
- `Pre_MatrixConcentration/SOURCE_FAITHFULNESS_LEDGER.md`: 4

## Category counts

- `build`: 7
- `build_cache`: 1
- `correspondence`: 2
- `correspondence_row`: 448
- `currentness`: 1
- `file_inventory`: 15
- `headline_axioms`: 18
- `history`: 1
- `import_graph`: 2
- `library_capability`: 1
- `machine_completion`: 4
- `merge_order`: 1
- `merge_reference`: 2
- `module_inventory`: 14
- `path`: 4
- `per_file_status`: 14
- `provenance`: 1
- `result_status`: 5
- `review_inventory`: 3
- `review_reference`: 60
- `semantic_faithfulness`: 16
- `source_inventory`: 1
- `source_policy`: 1
- `source_scan`: 4
- `toolchain`: 1
- `warnings`: 1
- `whole_surface`: 4

## Evidence boundary

This audit proves document/source arithmetic, physical paths, current imports, source-token absence, V1/V2 build classification, and any exact V4 rows already available. It does not independently prove historical body preservation, correspondence to the TeX source, or mathematical completeness. Those claims are marked `UNVERIFIABLE` rather than inferred.
