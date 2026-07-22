# V2 — Import-graph completeness

**Verdict: PASS**

Every Lean file in the current 222-file library universe is checked by a
declared build surface. The graph has no unresolved local import, cycle,
duplicate physical path, trust-path deviation, or orphan. All ten files in
the real `MatrixConcentration/` directory are covered by the lakefile glob
and are also transitively reachable from the HDP root.

## Scope

The FILE-WALK UNIVERSE is defined verbatim as:

- every `.lean` file physically under `HighDimensionalProbability/`;
- every `.lean` file physically under the project-root real directory
  `MatrixConcentration/`;
- excluding `HighDimensionalProbability/Verification/**` and `.lake/**`.

The project-root `HighDimensionalProbability.lean` is a graph entry point
outside that physical-file count. There is no `MatrixConcentration.lean`
root module. `tmp/*.lean` and `.audit_work/**/*.lean` are enumerated
separately as scratch and are never counted as library.

## Method and calibration

`scripts/file_universe.py` performs the physical walk. `scripts/import_graph.py`
masks nested Lean comments and strings, parses all `import` commands, resolves
both local module roots, computes transitive closures and strongly connected
components, and checks an exact surface partition. It independently applies
the lakefile's `MatrixConcentration.+` glob to all ten MC modules.

Exact re-run commands, from the project root:

```bash
python3 -B HighDimensionalProbability/Verification/scripts/file_universe.py --paths \
  > HighDimensionalProbability/Verification/logs/recert_file_universe.txt
python3 -B HighDimensionalProbability/Verification/scripts/import_graph.py \
  --expect-count 222 \
  > HighDimensionalProbability/Verification/logs/recert_import_graph.txt
python3 -B HighDimensionalProbability/Verification/scripts/import_graph.py \
  --expect-count 222 --json \
  > HighDimensionalProbability/Verification/logs/recert_import_graph.json
python3 -B HighDimensionalProbability/Verification/scripts/test_import_graph.py
python3 -B HighDimensionalProbability/Verification/scripts/v2_orphan_summary.py
```

Fresh recertification outputs are
[`logs/recert_file_universe.txt`](logs/recert_file_universe.txt),
[`logs/recert_import_graph.txt`](logs/recert_import_graph.txt),
[`logs/recert_import_graph.json`](logs/recert_import_graph.json),
[`logs/import_graph_recertification_calibration.log`](logs/import_graph_recertification_calibration.log),
and
[`logs/v2_orphan_recertification_summary.log`](logs/v2_orphan_recertification_summary.log).

The six positive calibrations prove that the parser finds a planted live
unresolved import while ignoring comment/string decoys, resolves both local
module roots to current physical paths, computes transitive reachability, and
detects a planted two-node cycle. All six pass.

## Results

| Measurement | Current result |
|---|---:|
| HDP physical files | 212 |
| MatrixConcentration physical files | 10 |
| **FILE-WALK UNIVERSE** | **222** |
| graph nodes including the one root module | 223 |
| syntactic imports | 911 |
| resolved local import edges | 429 |
| external import references | 482 |
| unresolved local imports | 0 |
| import cycles | 0 |
| HDP-root-reachable files | 111 |
| MC glob-built files | 10 |
| MC files also HDP-root-reachable | 10 |
| Appendix closure, including shared dependencies | 144 |
| shared root/Appendix dependencies | 33 |
| intentionally isolated Appendix-only files | 111 |
| glob-only MC files | 0 |
| **orphans** | **0** |
| **exclusive partition total** | **222** |

The exclusive surface classes are 111 root-reachable files plus 111
Appendix-only files. The ten MC files carry an additional `GLOB-BUILT` flag;
they are already within the root-reachable class, so they are not counted
twice in the partition.

The expected trust path has no deviation:

`HighDimensionalProbability` root → `ChapterN/Main.lean` →
`ChapterN_<ConsolidatedTitle>.lean`.

All nine wrappers follow it. Chapter 2 additionally imports
`Prelude.Orlicz`; this does not bypass its consolidated module. The HDP root
does not import the isolated Appendix. Five measured HDP-to-MC import edges
establish the vendored library's trust-path role.

The unified `Exercise/Chapter1`--`Exercise/Chapter9` subtree contributes all
67 expected Exercise modules. Every one resolves under the new
`HighDimensionalProbability.Exercise.ChapterN` module prefix and is reachable
from the HDP root; no legacy `ChapterN/Exercise` directory or import remains.

The final current-run scratch census comprises nine `tmp/*.lean` files and
37 `.audit_work/**/*.lean` files.  All 46 are classified separately from
library source; their paths appear in
[the recertified file-universe inventory](logs/recert_file_universe.txt).
`run_all.sh` re-enumerates this same scratch surface and fails on drift.

## Findings

| ID | Severity | Finding | Evidence |
|---|---|---|---|
| None | None | No findings. | `logs/recert_import_graph.txt`; `logs/v2_orphan_recertification_summary.log` |

## Limitations

This is a calibrated syntactic import and build-surface analysis. It proves
that every physical file is selected by a build surface and that local import
edges resolve; V1 proves those selected targets actually elaborate. It does
not prove declaration-level semantic dependence or mathematical meaning,
which are covered by V4, V6, and V7.
