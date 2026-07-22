# V2 — Import-graph completeness

**Verdict: PASS-WITH-NOTES**

**Tier: machine**

**Finding count: C=0 M=0 m=0 I=4**

## Guarantee

Every Lean file in the declared file-walk universe is reachable from the root
module. There is no unbuilt orphan in which an error, placeholder, or axiom
could hide.

## Method

From the project root:

```sh
python3 MatrixConcentration/Verification/scripts/source_manifest.py check
python3 MatrixConcentration/Verification/scripts/import_graph.py
```

The script includes every `.lean` file physically below the project root and
excludes exactly `.lake/**`, `MatrixConcentration/Verification/**`, and
`.audit_work/**`. It maps paths to Lean module names, parses all `import`
commands, computes the transitive closure from root module
`MatrixConcentration`, checks for in-universe symlinks, and records the
excluded audit scratch separately.

This definition intentionally excludes the audit's own Lean harnesses and
positive controls. It does not walk the parent workspace or the sibling
HighDimensionalProbability project.

## Results

| Classification | Count |
|---|---:|
| File-walk universe | 15 |
| Root-reachable | 15 |
| Orphans | 0 |
| In-universe symlinks | 0 |
| Explicit exclusions | 0 library files |

The universe is the root `MatrixConcentration.lean`, the shared Prelude, eight
chapter modules, and five appendix modules. The root directly imports all 14
inner modules; the script additionally records their project-local dependency
edges. The full per-file classification is in
[`logs/import_graph.txt`](logs/import_graph.txt) and its structured form is
[`logs/import_graph.json`](logs/import_graph.json).

The audit-scratch section of the raw log enumerates every file or symlink
under `.audit_work/` present when V2 ran; control markers are repeated in a
separate subsection for clarity. That excluded area grows as later V6/V7
review and `run_all.sh` stages record their evidence, so it is deliberately
reported as an enumeration rather than a fixed library count. macOS
`Icon\r` junk is listed there but ignored by content scanners.

### Final post-correction re-certification

The scope-corrected source manifest currently has digest
`38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89`.
The final lifecycle-bound import-graph replay found 15/15 root-reachable
files, zero orphans, and zero in-universe symlinks. It ran inside fresh
aggregate `8212cc84-aad8-4abc-b0df-b68fd3241112`, whose 21 numbered stages
plus final V2 refresh and consistency check produced 23 `START`, 23 `PASS`,
zero `FAIL`, and zero `SKIP`, with source digest above and
verification-input digest
`119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf`.
No source-layout finding changed in the correction. The independent final
lifecycle checker passed with zero problems, 14/14 final-claims files, and no
writer lock or finalization guard present.

### Adjacent non-Lean human-review record

`MatrixConcentration/HUMAN_VERIFICATION_LOG.md` exists beside the source
modules and currently contains `PENDING` entries. It is not a `.lean` file, is
not in the 15-file FILE-WALK UNIVERSE, and is not one of the 20 inputs pinned
by `logs/source_manifest.txt`. It is a separate, unfinished human-review
workflow: its status neither weakens this mechanical import-graph result nor
counts as completed human review. These three scope facts are recorded
explicitly in both import-graph logs.

### Audit-process note (not a library finding)

Two read-only `git status` commands were inadvertently invoked during
orientation and final continuation despite this pass's no-git rule. They
performed no `add`, commit, branch, checkout, or other repository mutation,
and no Git output is used as evidence. The zero-commit/Google-Drive setting
remains outside the snapshot mechanism: every verdict is tied instead to the
20-input SHA-256 source manifest, which is checked before and after long
runners. This procedural note does not change the four measured V2
environment findings or any library-soundness verdict.

## Findings

### V2-F1 — INFO — Stale parent scaffold exists

The parent workspace contains a different `lakefile.toml` and a stale
`MatrixConcentration.lean` whose docstring calls it a build sanity check. It
was neither built nor counted. This is an environment disambiguation note, not
a defect in the verified project.

### V2-F2 — INFO — Sibling name collisions are excluded

At this run, the HighDimensionalProbability sibling's top-level
`MatrixConcentration/` directory contains 10 flat `.lean` files. Contrary to
an older workspace description, the sibling has no top-level
`Pre_MatrixConcentration/` directory and no top-level
`MatrixConcentration.lean`. It does have two differently scoped files under
`HighDimensionalProbability/Prelude/` named `MatrixConcentration.lean` and
`MatrixConcentrationReal.lean`. The machine log records all of these exact
run-time facts. None of these sibling paths was read for source counts or
built. This records the contamination risk for future auditors without making
an unrelated sibling's volatile contents part of this project's verified
surface.

### V2-F3 — INFO — Project-root README is template boilerplate

The project-root `README.md` contains GitHub setup instructions and no
mathematical claims. The claims source for V9 is
`MatrixConcentration/README.md`.

### V2-F4 — INFO — Audit scratch is intentionally excluded

`.audit_work/` contains the positive-control sources created by
`make_calibration_plants.py` and V1 control markers. Its exclusion prevents
the audit from flagging its own deliberately bad declarations.

## Raw evidence

- [`logs/import_graph.txt`](logs/import_graph.txt) — human-readable complete
  enumeration and environment notes.
- [`logs/import_graph.json`](logs/import_graph.json) — structured graph,
  classifications, exclusions, scratch list, exact sibling inventory, and
  human-review-record scope flags.
- [`logs/environment.txt`](logs/environment.txt) — canonical/stale-tree
  evidence.
- [`logs/source_manifest.txt`](logs/source_manifest.txt) — the 20-input
  snapshot whose top-level digest this re-certification uses.
- [`logs/final_lifecycle_check.txt`](logs/final_lifecycle_check.txt) — terminal
  lifecycle/report acceptance certificate: `problems=0`, `result=PASS`, final
  claims manifest 14/14, and lock/guard checks clear.

## Limitations

The import parser recognizes the ordinary top-level `import Module.Name`
syntax used by this project. Reachability proves that each file is in the root
dependency graph; V1 supplies the independent evidence that those modules
actually elaborated. Generated code outside the declared file-walk universe
is not library source and is not covered by this result.

The sibling inventory is an environment-disambiguation snapshot, not a claim
about that other project's completeness. The pending human-verification log
is deliberately outside this mechanical check; no conclusion about completion
of that separate human workflow is drawn here.
