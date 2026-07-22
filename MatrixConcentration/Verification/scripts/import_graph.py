#!/usr/bin/env python3
"""Enumerate the declared Lean universe and prove root import reachability."""

from __future__ import annotations

from collections import defaultdict, deque
import json
from pathlib import Path
import re
import sys


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
WORK = ROOT / ".audit_work"
LOGS = VERIFY / "logs"
PARENT = ROOT.parent

EXCLUDED = (
    Path(".lake"),
    Path("MatrixConcentration/Verification"),
    Path(".audit_work"),
)
IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.'«»]+)\s*(?:--.*)?$")


def excluded(relative: Path) -> bool:
    return any(relative == prefix or prefix in relative.parents for prefix in EXCLUDED)


def universe() -> list[Path]:
    return sorted(
        (
            path.relative_to(ROOT)
            for path in ROOT.rglob("*.lean")
            if not excluded(path.relative_to(ROOT))
        ),
        key=lambda path: path.as_posix(),
    )


def module_name(path: Path) -> str:
    without_suffix = path.with_suffix("")
    return ".".join(without_suffix.parts)


def imports(path: Path) -> list[str]:
    found: list[str] = []
    for line in (ROOT / path).read_text(encoding="utf-8").splitlines():
        match = IMPORT.match(line)
        if match:
            found.append(match.group(1).replace("«", "").replace("»", ""))
    return found


def main() -> int:
    files = universe()
    modules = {module_name(path): path for path in files}
    project_edges: dict[str, list[str]] = {}
    external_edges: dict[str, list[str]] = {}
    reverse: dict[str, list[str]] = defaultdict(list)
    for module, path in modules.items():
        all_imports = imports(path)
        project_edges[module] = sorted(name for name in all_imports if name in modules)
        external_edges[module] = sorted(name for name in all_imports if name not in modules)
        for target in project_edges[module]:
            reverse[target].append(module)

    root_module = "MatrixConcentration"
    reachable: set[str] = set()
    queue: deque[str] = deque([root_module])
    while queue:
        module = queue.popleft()
        if module in reachable:
            continue
        reachable.add(module)
        queue.extend(project_edges.get(module, ()))

    orphans = sorted(set(modules) - reachable)
    symlinks = sorted(
        path.relative_to(ROOT).as_posix()
        for path in ROOT.rglob("*")
        if path.is_symlink() and not excluded(path.relative_to(ROOT))
    )
    scratch = sorted(
        path.relative_to(ROOT).as_posix()
        for path in WORK.rglob("*")
        if (path.is_file() or path.is_symlink())
    )
    scratch_controls = sorted(
        path.relative_to(ROOT).as_posix()
        for path in WORK.rglob("*.marker")
        if path.is_file()
    ) + sorted(
        path.relative_to(ROOT).as_posix()
        for path in WORK.rglob("*.done")
        if path.is_file()
    )
    root_readme = (ROOT / "README.md").read_text(encoding="utf-8")
    stale_parent = (
        (PARENT / "lakefile.toml").is_file()
        and (PARENT / "MatrixConcentration.lean").is_file()
        and "only serves as a build sanity check"
        in (PARENT / "MatrixConcentration.lean").read_text(encoding="utf-8")
    )
    hdp = PARENT / "HighDimensionalProbability"
    sibling_matrix_dir = hdp / "MatrixConcentration"
    sibling_flat_lean = sorted(
        path.name
        for path in sibling_matrix_dir.glob("*.lean")
        if path.is_file()
    ) if sibling_matrix_dir.is_dir() else []
    sibling_pre = hdp / "Pre_MatrixConcentration"
    sibling_root_lean = hdp / "MatrixConcentration.lean"
    sibling_nested_named_lean = sorted(
        str(path)
        for path in hdp.rglob("MatrixConcentration*.lean")
        if path != sibling_root_lean
    ) if hdp.is_dir() else []
    sibling_copies = [
        path
        for path in (
            sibling_matrix_dir,
            sibling_pre,
            sibling_root_lean,
        )
        if path.exists()
    ]
    human_log = ROOT / "MatrixConcentration" / "HUMAN_VERIFICATION_LOG.md"
    human_log_text = (
        human_log.read_text(encoding="utf-8", errors="replace")
        if human_log.is_file()
        else ""
    )

    data = {
        "rules": {
            "include": "every .lean file physically under the project root",
            "exclude": [f"{prefix.as_posix()}/**" for prefix in EXCLUDED],
        },
        "universe_count": len(files),
        "reachable_count": len(reachable & set(modules)),
        "orphan_count": len(orphans),
        "symlink_count": len(symlinks),
        "audit_work_count": len(scratch),
        "files": [
            {
                "path": path.as_posix(),
                "module": module_name(path),
                "classification": (
                    "ROOT-REACHABLE" if module_name(path) in reachable else "ORPHAN"
                ),
                "project_imports": project_edges[module_name(path)],
                "external_imports": external_edges[module_name(path)],
            }
            for path in files
        ],
        "orphans": orphans,
        "symlinks": symlinks,
        "audit_work": scratch,
        "audit_control_markers": scratch_controls,
        "environment": {
            "stale_parent_scaffold_confirmed": stale_parent,
            "stale_sibling_copy_count": len(sibling_copies),
            "stale_sibling_copies": [str(path) for path in sibling_copies],
            "sibling_matrixconcentration_flat_lean_count": len(sibling_flat_lean),
            "sibling_matrixconcentration_flat_lean": sibling_flat_lean,
            "sibling_pre_matrixconcentration_exists": sibling_pre.exists(),
            "sibling_root_matrixconcentration_lean_exists": sibling_root_lean.exists(),
            "sibling_nested_matrixconcentration_named_lean": sibling_nested_named_lean,
            "root_readme_is_github_template": (
                "To set up your new GitHub repository" in root_readme
                and "## GitHub configuration" in root_readme
            ),
            "human_verification_log_exists": human_log.is_file(),
            "human_verification_log_pending": "PENDING" in human_log_text,
            "human_verification_log_in_file_walk_universe": False,
            "human_verification_log_in_source_manifest": False,
        },
    }
    json_path = LOGS / "import_graph.json"
    json_path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    lines = [
        "V2 IMPORT-GRAPH COMPLETENESS",
        "INCLUDE every .lean file physically under the project root",
        "EXCLUDE .lake/**, MatrixConcentration/Verification/**, .audit_work/**",
        f"UNIVERSE {len(files)}",
        f"ROOT_REACHABLE {len(reachable & set(modules))}",
        f"ORPHANS {len(orphans)}",
        f"SYMLINKS {len(symlinks)}",
        f"AUDIT_WORK_FILES {len(scratch)}",
        "",
        "FILES",
    ]
    for item in data["files"]:
        lines.append(
            f"{item['classification']}\t{item['module']}\t{item['path']}\t"
            f"imports={','.join(item['project_imports']) or '-'}"
        )
    lines.extend(
        [
            "",
            "ORPHAN_MODULES",
            *(orphans or ["NONE"]),
            "",
            "IN_UNIVERSE_SYMLINKS",
            *(symlinks or ["NONE"]),
            "",
            "AUDIT_SCRATCH",
            *(scratch or ["NONE"]),
            "",
            "AUDIT_CONTROL_MARKERS",
            *(scratch_controls or ["NONE"]),
            "",
            "ENVIRONMENT_NOTES",
            f"stale_parent_scaffold_confirmed={str(stale_parent).lower()}",
            f"stale_sibling_copy_count={len(sibling_copies)}",
            *(str(path) for path in sibling_copies),
            "sibling_matrixconcentration_flat_lean_count="
            f"{len(sibling_flat_lean)}",
            "sibling_matrixconcentration_flat_lean="
            f"{','.join(sibling_flat_lean) or '-'}",
            "sibling_pre_matrixconcentration_exists="
            f"{str(sibling_pre.exists()).lower()}",
            "sibling_root_matrixconcentration_lean_exists="
            f"{str(sibling_root_lean.exists()).lower()}",
            "sibling_nested_matrixconcentration_named_lean="
            f"{','.join(sibling_nested_named_lean) or '-'}",
            "root_readme_is_github_template="
            f"{str(data['environment']['root_readme_is_github_template']).lower()}",
            "human_verification_log_exists="
            f"{str(human_log.is_file()).lower()}",
            "human_verification_log_pending="
            f"{str('PENDING' in human_log_text).lower()}",
            "human_verification_log_in_file_walk_universe=false",
            "human_verification_log_in_source_manifest=false",
        ]
    )
    text_path = LOGS / "import_graph.txt"
    text_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))

    passed = (
        len(files) == 15
        and len(reachable & set(modules)) == 15
        and not orphans
        and not symlinks
        and stale_parent
        and data["environment"]["root_readme_is_github_template"]
    )
    print(f"VERDICT {'PASS' if passed else 'FAIL'}")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
