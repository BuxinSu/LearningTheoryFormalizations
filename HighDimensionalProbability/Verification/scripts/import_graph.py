#!/usr/bin/env python3
"""Audit local Lean imports and partition the complete verification universe.

The source universe comes exclusively from :mod:`file_universe`.
MatrixConcentration modules are walked through the real project-root
``MatrixConcentration/`` directory, and ``Verification/**`` is excluded.

The sole project-root module is an entry point but is not a member of the
file-walk universe.  The MatrixConcentration library has no root module: its
lakefile glob builds all ten physical modules.  Each universe file receives
the relevant reachability/build flags and exactly one surface class:

* ``root-reachable`` -- transitively imported by the HDP root module;
* ``glob-built`` -- not root-reachable, but built by the MC library glob;
* ``explicit Appendix-only`` -- in the explicitly built Appendix closure and
  neither root-reachable nor already covered by the MC glob;
* ``orphan`` -- reached or built by none of those entry-point classes.

The script emits all category paths, resolved local edges, unresolved local
imports, import cycles, cross-library edges, and the expected HDP
``root -> ChapterN.Main -> consolidated ChapterN`` trust shape.  It exits
nonzero if the universe does not form an exact partition or if another graph
integrity invariant fails.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence

from file_universe import HDP, MC, ROOT, enumerate_universe


HDP_MODULE_ROOT = "HighDimensionalProbability"
MC_MODULE_ROOT = "MatrixConcentration"
LOCAL_MODULE_ROOTS = {HDP_MODULE_ROOT, MC_MODULE_ROOT}

HDP_ROOT_PATH = "HighDimensionalProbability.lean"
APPENDIX_ROOT_PATH = "HighDimensionalProbability/Appendix.lean"

IMPORT_RE = re.compile(r"(?m)^[ \t]*import[ \t]+(?P<payload>[^\r\n]+)")
ORDINARY_NAME_SEGMENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


@dataclass(frozen=True, order=True)
class ImportRef:
    """One syntactic import in a Lean source file."""

    source_path: str
    line: int
    module: str


@dataclass(frozen=True, order=True)
class LocalEdge:
    """One resolved project-local import edge."""

    source_path: str
    source_module: str
    line: int
    import_module: str
    target_path: str
    target_module: str


@dataclass(frozen=True, order=True)
class UnresolvedImport:
    """A local-root import whose expected physical source is unavailable."""

    source_path: str
    line: int
    module: str
    expected_path: str
    reason: str


def display_path(path: Path) -> str:
    """Return a deterministic project-root-relative POSIX path."""

    return path.relative_to(ROOT).as_posix()


def split_module_name(module: str) -> list[str]:
    """Split a Lean module name at dots outside ``«quoted segments»``."""

    parts: list[str] = []
    current: list[str] = []
    quoted = False
    for char in module:
        if char == "«" and not quoted:
            quoted = True
            current.append(char)
        elif char == "»" and quoted:
            quoted = False
            current.append(char)
        elif char == "." and not quoted:
            if not current:
                raise ValueError(f"empty module-name segment in {module!r}")
            parts.append("".join(current))
            current = []
        else:
            current.append(char)
    if quoted:
        raise ValueError(f"unterminated quoted module-name segment in {module!r}")
    if not current:
        raise ValueError(f"empty final module-name segment in {module!r}")
    parts.append("".join(current))
    return parts


def unquote_segment(segment: str) -> str:
    if segment.startswith("«") and segment.endswith("»"):
        return segment[1:-1]
    if "«" in segment or "»" in segment:
        raise ValueError(f"malformed quoted module-name segment {segment!r}")
    return segment


def quote_segment(segment: str) -> str:
    if ORDINARY_NAME_SEGMENT_RE.fullmatch(segment):
        return segment
    return f"«{segment}»"


def module_to_expected_path(module: str) -> str | None:
    """Resolve an HDP/MC module name to its canonical physical source path.

    MatrixConcentration maps directly to the real project-root directory.
    """

    parts = split_module_name(module)
    if not parts or parts[0] not in LOCAL_MODULE_ROOTS:
        return None
    if len(parts) == 1:
        return f"{parts[0]}.lean"
    tail = [unquote_segment(part) for part in parts[1:]]
    base = HDP if parts[0] == HDP_MODULE_ROOT else MC
    path = base.joinpath(*tail)
    return display_path(Path(f"{path}.lean"))


def path_to_module(path: str) -> str:
    """Map a canonical physical project path back to its Lean module name."""

    if path == HDP_ROOT_PATH:
        return HDP_MODULE_ROOT
    source = ROOT / path
    if source.is_relative_to(HDP):
        parts = source.relative_to(HDP).with_suffix("").parts
        return ".".join([HDP_MODULE_ROOT, *(quote_segment(part) for part in parts)])
    if source.is_relative_to(MC):
        parts = source.relative_to(MC).with_suffix("").parts
        return ".".join([MC_MODULE_ROOT, *(quote_segment(part) for part in parts)])
    raise ValueError(f"path is outside both local module roots: {path}")


def mask_comments_and_strings(text: str, *, source: str) -> str:
    """Mask nested Lean comments and strings while preserving line offsets."""

    masked = list(text)
    length = len(text)
    index = 0

    def blank(start: int, end: int) -> None:
        for position in range(start, end):
            if masked[position] not in "\r\n":
                masked[position] = " "

    while index < length:
        if text.startswith("--", index):
            end = text.find("\n", index + 2)
            if end == -1:
                end = length
            blank(index, end)
            index = end
            continue

        if text.startswith("/-", index):
            start = index
            depth = 1
            index += 2
            while index < length and depth:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise ValueError(f"{source}: unterminated block comment")
            blank(start, index)
            continue

        if text[index] == '"':
            start = index
            index += 1
            while index < length:
                if text[index] == "\\":
                    index = min(length, index + 2)
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            else:
                raise ValueError(f"{source}: unterminated string literal")
            blank(start, index)
            continue

        index += 1

    return "".join(masked)


def split_import_payload(payload: str, *, source: str, line: int) -> list[str]:
    """Split one import payload, retaining whitespace inside quoted segments."""

    modules: list[str] = []
    current: list[str] = []
    quoted = False
    for char in payload.strip():
        if char == "«" and not quoted:
            quoted = True
            current.append(char)
        elif char == "»" and quoted:
            quoted = False
            current.append(char)
        elif char.isspace() and not quoted:
            if current:
                modules.append("".join(current))
                current = []
        else:
            current.append(char)
    if quoted:
        raise ValueError(f"{source}:{line}: unterminated quoted import segment")
    if current:
        modules.append("".join(current))
    if not modules:
        raise ValueError(f"{source}:{line}: import command has no module")
    return modules


def parse_imports(path: str) -> list[ImportRef]:
    """Parse every import command in one project source file."""

    text = (ROOT / path).read_text(encoding="utf-8")
    masked = mask_comments_and_strings(text, source=path)
    imports: list[ImportRef] = []
    for match in IMPORT_RE.finditer(masked):
        line = masked.count("\n", 0, match.start()) + 1
        for module in split_import_payload(match.group("payload"), source=path, line=line):
            # Validate quoted-segment syntax even for external modules.
            split_module_name(module)
            imports.append(ImportRef(path, line, module))
    return imports


def transitive_closure(starts: Iterable[str], graph: dict[str, set[str]]) -> set[str]:
    """Compute the graph closure of ``starts`` iteratively."""

    reached: set[str] = set()
    stack = list(starts)
    while stack:
        node = stack.pop()
        if node in reached:
            continue
        reached.add(node)
        stack.extend(sorted(graph.get(node, ()), reverse=True))
    return reached


def strongly_connected_components(graph: dict[str, set[str]]) -> list[list[str]]:
    """Return every cyclic strongly connected component deterministically."""

    next_index = 0
    indices: dict[str, int] = {}
    lowlinks: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    components: list[list[str]] = []

    def visit(node: str) -> None:
        nonlocal next_index
        indices[node] = next_index
        lowlinks[node] = next_index
        next_index += 1
        stack.append(node)
        on_stack.add(node)

        for target in sorted(graph.get(node, ())):
            if target not in indices:
                visit(target)
                lowlinks[node] = min(lowlinks[node], lowlinks[target])
            elif target in on_stack:
                lowlinks[node] = min(lowlinks[node], indices[target])

        if lowlinks[node] != indices[node]:
            return
        component: list[str] = []
        while True:
            member = stack.pop()
            on_stack.remove(member)
            component.append(member)
            if member == node:
                break
        component.sort()
        if len(component) > 1 or node in graph.get(node, set()):
            components.append(component)

    for node in sorted(graph):
        if node not in indices:
            visit(node)
    return sorted(components)


def library_of(path: str) -> str:
    if path == HDP_ROOT_PATH or path.startswith("HighDimensionalProbability/"):
        return HDP_MODULE_ROOT
    if path.startswith("MatrixConcentration/"):
        return MC_MODULE_ROOT
    raise ValueError(f"unknown local library path: {path}")


def inventory_entry(
    path: str,
    *,
    hdp_reachable: set[str],
    glob_built: set[str],
    surface_class: str,
) -> dict[str, object]:
    return {
        "path": path,
        "module": path_to_module(path),
        "library": library_of(path),
        "root_reachable": path in hdp_reachable,
        "glob_built": path in glob_built,
        "surface_class": surface_class,
    }


def build_trust_shape(
    imports_by_path: dict[str, list[ImportRef]],
    hdp_reachable: set[str],
    appendix_closure: set[str],
    local_edges: Sequence[LocalEdge],
) -> dict[str, object]:
    """Describe and validate the expected root/wrapper/consolidated shape."""

    deviations: list[str] = []
    root_imports = [item.module for item in imports_by_path.get(HDP_ROOT_PATH, [])]
    chapters: list[dict[str, object]] = []

    for chapter in range(1, 10):
        wrapper_module = f"{HDP_MODULE_ROOT}.Chapter{chapter}.Main"
        wrapper_path = module_to_expected_path(wrapper_module)
        assert wrapper_path is not None
        wrapper_imports = [
            item.module for item in imports_by_path.get(wrapper_path, [])
        ]
        consolidated_prefix = f"{HDP_MODULE_ROOT}.Chapter{chapter}_"
        consolidated = sorted(
            module for module in wrapper_imports if module.startswith(consolidated_prefix)
        )
        extra_local = sorted(
            module
            for module in wrapper_imports
            if split_module_name(module)[0] in LOCAL_MODULE_ROOTS
            and module not in consolidated
        )
        root_has_wrapper = wrapper_module in root_imports
        target_paths = [
            module_to_expected_path(module)
            for module in consolidated
            if module_to_expected_path(module) is not None
        ]
        targets_exist = all((ROOT / path).is_file() for path in target_paths)
        status = (
            "PASS"
            if root_has_wrapper and len(consolidated) == 1 and targets_exist
            else "DEVIATION"
        )
        if not root_has_wrapper:
            deviations.append(f"HDP root does not import {wrapper_module}")
        if len(consolidated) != 1:
            deviations.append(
                f"{wrapper_module} imports {len(consolidated)} consolidated Chapter "
                f"{chapter} modules, expected exactly one"
            )
        if not targets_exist:
            deviations.append(f"{wrapper_module} has a missing consolidated target")
        chapters.append(
            {
                "chapter": chapter,
                "status": status,
                "root_imports_wrapper": root_has_wrapper,
                "wrapper_module": wrapper_module,
                "wrapper_path": wrapper_path,
                "consolidated_imports": consolidated,
                "consolidated_paths": target_paths,
                "additional_local_wrapper_imports": extra_local,
            }
        )

    appendix_prefix_paths = {
        APPENDIX_ROOT_PATH,
        *(
            path
            for path in hdp_reachable | appendix_closure
            if path.startswith("HighDimensionalProbability/Appendix/")
        ),
    }
    appendix_in_hdp_root = sorted(appendix_prefix_paths & hdp_reachable)
    if appendix_in_hdp_root:
        deviations.append(
            "HDP root reaches the isolated Appendix: " + ", ".join(appendix_in_hdp_root)
        )

    cross_library_edges = [
        asdict(edge)
        for edge in local_edges
        if library_of(edge.source_path) != library_of(edge.target_path)
    ]
    hdp_to_mc_edges = [
        edge
        for edge in cross_library_edges
        if edge["source_path"] in hdp_reachable
        and edge["target_path"].startswith("MatrixConcentration/")
    ]

    return {
        "expected_shape": (
            "HighDimensionalProbability root -> ChapterN/Main.lean -> "
            "ChapterN_<ConsolidatedTitle>.lean"
        ),
        "chapter_wrappers": chapters,
        "hdp_root_direct_imports": root_imports,
        "matrix_root_direct_imports": [],
        "matrix_root_module_exists": False,
        "appendix_isolated_from_hdp_root": not appendix_in_hdp_root,
        "appendix_paths_reached_by_hdp_root": appendix_in_hdp_root,
        "cross_library_edges": cross_library_edges,
        "hdp_root_trust_path_entries_into_mc": hdp_to_mc_edges,
        "deviations": deviations,
    }


def audit_import_graph(*, expected_count: int | None) -> dict[str, object]:
    """Build the graph, exact partition, and integrity diagnostics."""

    universe_data = enumerate_universe()
    raw_universe = universe_data["file_walk_universe"]
    raw_roots = universe_data["root_modules_separate"]
    assert isinstance(raw_universe, list)
    assert isinstance(raw_roots, list)
    universe_paths = [str(path) for path in raw_universe]
    root_paths = [str(path) for path in raw_roots]

    validation_errors: list[str] = []
    parse_errors: list[str] = []

    if len(universe_paths) != len(set(universe_paths)):
        validation_errors.append("file_universe returned duplicate relative paths")

    realpath_groups: dict[str, list[str]] = defaultdict(list)
    for path in universe_paths:
        source = ROOT / path
        if not source.is_file():
            validation_errors.append(f"universe path is not a file: {path}")
            continue
        realpath_groups[str(source.resolve())].append(path)
    duplicate_realpaths = {
        realpath: sorted(paths)
        for realpath, paths in realpath_groups.items()
        if len(paths) > 1
    }
    if duplicate_realpaths:
        validation_errors.append(
            f"universe contains {len(duplicate_realpaths)} duplicated physical paths"
        )

    if expected_count is not None and len(universe_paths) != expected_count:
        validation_errors.append(
            f"file-walk universe count is {len(universe_paths)}, expected {expected_count}"
        )

    expected_roots = {HDP_ROOT_PATH}
    if set(root_paths) != expected_roots:
        validation_errors.append(
            f"root module inventory is {sorted(root_paths)!r}, expected "
            f"{sorted(expected_roots)!r}"
        )

    node_paths = sorted(set(universe_paths) | expected_roots)
    universe_set = set(universe_paths)
    node_set = set(node_paths)

    module_to_path: dict[str, str] = {}
    duplicate_modules: dict[str, list[str]] = defaultdict(list)
    for path in node_paths:
        try:
            module = path_to_module(path)
        except ValueError as error:
            validation_errors.append(str(error))
            continue
        if module in module_to_path:
            duplicate_modules[module].extend([module_to_path[module], path])
        else:
            module_to_path[module] = path
    duplicate_modules = {
        module: sorted(set(paths)) for module, paths in duplicate_modules.items()
    }
    if duplicate_modules:
        validation_errors.append(
            f"{len(duplicate_modules)} Lean module names map to multiple physical files"
        )

    imports_by_path: dict[str, list[ImportRef]] = {}
    local_edges: list[LocalEdge] = []
    unresolved: list[UnresolvedImport] = []
    external_imports: list[ImportRef] = []
    graph: dict[str, set[str]] = {path: set() for path in node_paths}

    for source_path in node_paths:
        try:
            imports = parse_imports(source_path)
        except (OSError, UnicodeError, ValueError) as error:
            imports = []
            parse_errors.append(str(error))
        imports_by_path[source_path] = imports
        for imported in imports:
            try:
                module_parts = split_module_name(imported.module)
                expected_path = module_to_expected_path(imported.module)
            except ValueError as error:
                parse_errors.append(f"{source_path}:{imported.line}: {error}")
                continue
            if module_parts[0] not in LOCAL_MODULE_ROOTS:
                external_imports.append(imported)
                continue
            assert expected_path is not None
            if expected_path not in node_set:
                expected_source = ROOT / expected_path
                reason = (
                    "local source exists but is outside the verified graph"
                    if expected_source.is_file()
                    else "local source file does not exist"
                )
                unresolved.append(
                    UnresolvedImport(
                        source_path,
                        imported.line,
                        imported.module,
                        expected_path,
                        reason,
                    )
                )
                continue
            target_module = path_to_module(expected_path)
            edge = LocalEdge(
                source_path,
                path_to_module(source_path),
                imported.line,
                imported.module,
                expected_path,
                target_module,
            )
            local_edges.append(edge)
            graph[source_path].add(expected_path)

    local_edges.sort()
    unresolved.sort()
    external_imports.sort()
    if parse_errors:
        validation_errors.append(f"{len(parse_errors)} source/import parse errors")
    if unresolved:
        validation_errors.append(f"{len(unresolved)} unresolved project-local imports")

    hdp_closure_all = transitive_closure([HDP_ROOT_PATH], graph)
    hdp_reachable = hdp_closure_all & universe_set
    root_reachable = hdp_reachable
    glob_built = {
        path for path in universe_set if path.startswith("MatrixConcentration/")
    }

    if APPENDIX_ROOT_PATH not in universe_set:
        validation_errors.append(
            f"Appendix entry module is absent from the universe: {APPENDIX_ROOT_PATH}"
        )
        appendix_closure: set[str] = set()
    else:
        appendix_closure = (
            transitive_closure([APPENDIX_ROOT_PATH], graph) & universe_set
        )
    glob_only = glob_built - root_reachable
    explicit_appendix_only = appendix_closure - root_reachable - glob_built
    orphan = (
        universe_set
        - root_reachable
        - glob_only
        - explicit_appendix_only
    )

    categories = {
        "root-reachable": root_reachable,
        "glob-built": glob_only,
        "explicit Appendix-only": explicit_appendix_only,
        "orphan": orphan,
    }
    assigned: dict[str, list[str]] = defaultdict(list)
    for category, paths in categories.items():
        for path in paths:
            assigned[path].append(category)
    missing_from_partition = sorted(universe_set - set(assigned))
    multiply_classified = {
        path: sorted(category_names)
        for path, category_names in assigned.items()
        if len(category_names) != 1
    }
    unexpected_partition_paths = sorted(set(assigned) - universe_set)
    partition_count = sum(len(paths) for paths in categories.values())
    partition_ok = (
        not missing_from_partition
        and not multiply_classified
        and not unexpected_partition_paths
        and partition_count == len(universe_set)
    )
    if not partition_ok:
        validation_errors.append("file-walk universe does not form an exact partition")

    cycles = strongly_connected_components(graph)
    if cycles:
        validation_errors.append(f"local import graph contains {len(cycles)} cycles")

    trust_shape = build_trust_shape(
        imports_by_path, hdp_reachable, appendix_closure, local_edges
    )
    trust_deviations = trust_shape["deviations"]
    assert isinstance(trust_deviations, list)
    if trust_deviations:
        validation_errors.append(
            f"expected trust-path shape has {len(trust_deviations)} deviations"
        )

    physical_appendix_paths = {
        path
        for path in universe_set
        if path == APPENDIX_ROOT_PATH
        or path.startswith("HighDimensionalProbability/Appendix/")
    }
    appendix_prefix_not_in_closure = sorted(
        physical_appendix_paths - appendix_closure
    )

    root_entries = [
        inventory_entry(
            path,
            hdp_reachable=hdp_reachable,
            glob_built=glob_built,
            surface_class="ROOT-REACHABLE",
        )
        for path in sorted(root_reachable)
    ]
    glob_entries = [
        inventory_entry(
            path,
            hdp_reachable=hdp_reachable,
            glob_built=glob_built,
            surface_class="GLOB-BUILT",
        )
        for path in sorted(glob_only)
    ]
    appendix_entries = [
        inventory_entry(
            path,
            hdp_reachable=hdp_reachable,
            glob_built=glob_built,
            surface_class="INTENTIONALLY-EXCLUDED-BUILT-EXPLICITLY",
        )
        for path in sorted(explicit_appendix_only)
    ]
    orphan_entries = [
        inventory_entry(
            path,
            hdp_reachable=hdp_reachable,
            glob_built=glob_built,
            surface_class="ORPHAN",
        )
        for path in sorted(orphan)
    ]

    external_modules = sorted({item.module for item in external_imports})
    result: dict[str, object] = {
        "status": "PASS" if not validation_errors else "FAIL",
        "rules": universe_data["rules"],
        "entry_points": {
            "root_modules_separate": sorted(expected_roots),
            "appendix_entry_in_universe": APPENDIX_ROOT_PATH,
            "matrix_library_root_module": None,
            "matrix_library_glob": "MatrixConcentration.+",
            "matrix_modules_resolve_via": "MatrixConcentration/",
        },
        "counts": {
            "file_walk_universe": len(universe_set),
            "hdp_physical_files": len(universe_data["hdp"]),
            "matrix_concentration_physical_files": len(
                universe_data["matrix_concentration"]
            ),
            "graph_nodes_including_root_module": len(node_paths),
            "syntactic_imports": sum(len(items) for items in imports_by_path.values()),
            "resolved_local_import_edges": len(local_edges),
            "external_import_references": len(external_imports),
            "unique_external_modules": len(external_modules),
            "unresolved_local_imports": len(unresolved),
            "import_cycles": len(cycles),
            "root_reachable": len(root_reachable),
            "root_reachable_from_hdp": len(hdp_reachable),
            "matrix_concentration_glob_built": len(glob_built),
            "matrix_concentration_glob_only": len(glob_only),
            "matrix_concentration_also_root_reachable": len(
                glob_built & hdp_reachable
            ),
            "appendix_closure_including_shared_dependencies": len(appendix_closure),
            "shared_root_and_appendix_dependencies": len(
                root_reachable & appendix_closure
            ),
            "physical_appendix_paths_not_in_closure": len(
                appendix_prefix_not_in_closure
            ),
            "explicit_appendix_only": len(explicit_appendix_only),
            "orphan": len(orphan),
            "partition_total": partition_count,
        },
        "partition": {
            "status": "PASS" if partition_ok else "FAIL",
            "root_reachable": root_entries,
            "glob_built": glob_entries,
            "explicit_appendix_only": appendix_entries,
            "orphan": orphan_entries,
            "missing": missing_from_partition,
            "multiply_classified": multiply_classified,
            "unexpected_paths": unexpected_partition_paths,
        },
        "reachability": {
            "hdp_root": sorted(hdp_reachable),
            "matrix_concentration_glob": sorted(glob_built),
            "matrix_concentration_also_hdp_root_reachable": sorted(
                glob_built & hdp_reachable
            ),
            "appendix_closure": sorted(appendix_closure),
            "shared_root_and_appendix_dependencies": sorted(
                root_reachable & appendix_closure
            ),
            "physical_appendix_paths_not_in_closure": appendix_prefix_not_in_closure,
        },
        "local_edges": [asdict(edge) for edge in local_edges],
        "unresolved_local_imports": [asdict(item) for item in unresolved],
        "external_imports": {
            "unique_modules": external_modules,
            "references": [asdict(item) for item in external_imports],
        },
        "cycles": cycles,
        "trust_shape": trust_shape,
        "diagnostics": {
            "parse_errors": sorted(parse_errors),
            "duplicate_realpaths": duplicate_realpaths,
            "duplicate_modules": duplicate_modules,
            "validation_errors": validation_errors,
        },
    }
    return result


def render_inventory(lines: list[str], title: str, entries: object) -> None:
    assert isinstance(entries, list)
    lines.extend(("", f"[{title}] count={len(entries)}"))
    if not entries:
        lines.append("none")
        return
    for raw_entry in entries:
        assert isinstance(raw_entry, dict)
        lines.append(
            f"{raw_entry['module']}\t{raw_entry['path']}\t"
            f"library={raw_entry['library']}\t"
            f"class={raw_entry['surface_class']}\t"
            f"root_reachable={str(raw_entry['root_reachable']).lower()}\t"
            f"glob_built={str(raw_entry['glob_built']).lower()}"
        )


def render_text(data: dict[str, object]) -> str:
    """Render a self-contained, deterministic human-readable V2 log."""

    counts = data["counts"]
    partition = data["partition"]
    diagnostics = data["diagnostics"]
    assert isinstance(counts, dict)
    assert isinstance(partition, dict)
    assert isinstance(diagnostics, dict)

    lines = [
        "V2 IMPORT-GRAPH COMPLETENESS AUDIT",
        "==================================",
        f"status: {data['status']}",
        "universe: file_universe.py (HDP physical path + real MC directory; Verification excluded)",
        "root modules: HighDimensionalProbability.lean only (entry point, separate)",
        "appendix entry: HighDimensionalProbability/Appendix.lean (inside universe)",
        "MC build rule: lakefile glob MatrixConcentration.+; no MC root module",
        "MC resolution: MatrixConcentration.* -> MatrixConcentration/*.lean",
        "",
        "[counts]",
    ]
    count_order = (
        "file_walk_universe",
        "hdp_physical_files",
        "matrix_concentration_physical_files",
        "graph_nodes_including_root_module",
        "syntactic_imports",
        "resolved_local_import_edges",
        "external_import_references",
        "unique_external_modules",
        "unresolved_local_imports",
        "import_cycles",
        "root_reachable",
        "root_reachable_from_hdp",
        "matrix_concentration_glob_built",
        "matrix_concentration_glob_only",
        "matrix_concentration_also_root_reachable",
        "appendix_closure_including_shared_dependencies",
        "shared_root_and_appendix_dependencies",
        "physical_appendix_paths_not_in_closure",
        "explicit_appendix_only",
        "orphan",
        "partition_total",
    )
    lines.extend(f"{key}: {counts[key]}" for key in count_order)
    lines.append(f"partition_status: {partition['status']}")

    render_inventory(lines, "root-reachable", partition["root_reachable"])
    render_inventory(lines, "glob-built", partition["glob_built"])
    render_inventory(
        lines, "explicit Appendix-only", partition["explicit_appendix_only"]
    )
    render_inventory(lines, "orphan", partition["orphan"])

    reachability = data["reachability"]
    assert isinstance(reachability, dict)
    appendix_outside = reachability["physical_appendix_paths_not_in_closure"]
    assert isinstance(appendix_outside, list)
    lines.extend(
        (
            "",
            f"[physical_appendix_paths_not_in_closure] count={len(appendix_outside)}",
        )
    )
    lines.extend(appendix_outside or ["none"])

    local_edges = data["local_edges"]
    assert isinstance(local_edges, list)
    lines.extend(("", f"[resolved_local_edges] count={len(local_edges)}"))
    if not local_edges:
        lines.append("none")
    for raw_edge in local_edges:
        assert isinstance(raw_edge, dict)
        lines.append(
            f"{raw_edge['source_path']}:{raw_edge['line']}\t"
            f"{raw_edge['source_module']} -> {raw_edge['target_module']}\t"
            f"target={raw_edge['target_path']}"
        )

    unresolved = data["unresolved_local_imports"]
    assert isinstance(unresolved, list)
    lines.extend(("", f"[unresolved_local_imports] count={len(unresolved)}"))
    if not unresolved:
        lines.append("none")
    for raw_item in unresolved:
        assert isinstance(raw_item, dict)
        lines.append(
            f"{raw_item['source_path']}:{raw_item['line']}\t"
            f"{raw_item['module']}\texpected={raw_item['expected_path']}\t"
            f"reason={raw_item['reason']}"
        )

    cycles = data["cycles"]
    assert isinstance(cycles, list)
    lines.extend(("", f"[import_cycles] count={len(cycles)}"))
    if not cycles:
        lines.append("none")
    for index, cycle in enumerate(cycles, 1):
        assert isinstance(cycle, list)
        lines.append(f"cycle-{index}: {' -> '.join(cycle)}")

    trust_shape = data["trust_shape"]
    assert isinstance(trust_shape, dict)
    lines.extend(
        (
            "",
            "[trust_shape]",
            f"expected: {trust_shape['expected_shape']}",
            "appendix_isolated_from_hdp_root: "
            f"{str(trust_shape['appendix_isolated_from_hdp_root']).lower()}",
            "hdp_root_direct_imports: "
            + ", ".join(trust_shape["hdp_root_direct_imports"]),
            "matrix_root_module_exists: false",
            "matrix_library_glob: MatrixConcentration.+",
        )
    )
    chapter_wrappers = trust_shape["chapter_wrappers"]
    assert isinstance(chapter_wrappers, list)
    for raw_chapter in chapter_wrappers:
        assert isinstance(raw_chapter, dict)
        lines.append(
            f"chapter_{raw_chapter['chapter']}: {raw_chapter['status']}\t"
            f"{raw_chapter['wrapper_module']} -> "
            f"{','.join(raw_chapter['consolidated_imports'])}\t"
            f"additional_local={','.join(raw_chapter['additional_local_wrapper_imports']) or 'none'}"
        )

    cross_edges = trust_shape["cross_library_edges"]
    assert isinstance(cross_edges, list)
    lines.extend(("", f"[cross_library_edges] count={len(cross_edges)}"))
    if not cross_edges:
        lines.append("none")
    for raw_edge in cross_edges:
        assert isinstance(raw_edge, dict)
        lines.append(
            f"{raw_edge['source_path']}:{raw_edge['line']}\t"
            f"{raw_edge['source_module']} -> {raw_edge['target_module']}\t"
            f"target={raw_edge['target_path']}"
        )

    external = data["external_imports"]
    assert isinstance(external, dict)
    modules = external["unique_modules"]
    assert isinstance(modules, list)
    lines.extend(("", f"[external_import_modules] count={len(modules)}"))
    lines.extend(modules or ["none"])

    trust_deviations = trust_shape["deviations"]
    assert isinstance(trust_deviations, list)
    lines.extend(("", f"[trust_shape_deviations] count={len(trust_deviations)}"))
    lines.extend(trust_deviations or ["none"])

    errors = diagnostics["validation_errors"]
    assert isinstance(errors, list)
    lines.extend(("", f"[validation_errors] count={len(errors)}"))
    lines.extend(errors or ["none"])
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    parser.add_argument(
        "--expect-count",
        type=int,
        default=None,
        help="fail if the dynamic file-walk universe does not have this size",
    )
    args = parser.parse_args()

    data = audit_import_graph(expected_count=args.expect_count)
    if args.json:
        print(json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True))
    else:
        print(render_text(data), end="")
    return 0 if data["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
