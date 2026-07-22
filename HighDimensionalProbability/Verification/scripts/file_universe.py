#!/usr/bin/env python3
"""Enumerate the verification pass's source and scratch universes."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
HDP = ROOT / "HighDimensionalProbability"
MC = ROOT / "MatrixConcentration"
VERIFICATION = HDP / "Verification"


def _relative_lean_files(base: Path, *, exclude_verification: bool = False) -> list[str]:
    result: list[str] = []
    for path in base.rglob("*.lean"):
        if path.is_symlink() or not path.is_file():
            continue
        if exclude_verification and (path == VERIFICATION or VERIFICATION in path.parents):
            continue
        result.append(path.relative_to(ROOT).as_posix())
    return sorted(result)


def enumerate_universe() -> dict[str, object]:
    hdp = _relative_lean_files(HDP, exclude_verification=True)
    mc = _relative_lean_files(MC)
    library = sorted(hdp + mc)
    tmp = sorted(
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / "tmp").glob("*.lean")
        if path.is_file() and not path.is_symlink()
    )
    audit = sorted(
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / ".audit_work").rglob("*.lean")
        if path.is_file() and not path.is_symlink()
    )
    roots = [
        name
        for name in ("HighDimensionalProbability.lean",)
        if (ROOT / name).is_file()
    ]
    return {
        "rules": {
            "hdp": "every .lean physically below HighDimensionalProbability/, excluding Verification/**",
            "matrix_concentration": (
                "every .lean physically below the project-root MatrixConcentration/ "
                "real directory"
            ),
            "scratch": "tmp/*.lean and .audit_work/**/*.lean are enumerated separately",
            "always_excluded": [".lake/**", "HighDimensionalProbability/Verification/**"],
        },
        "counts": {
            "hdp": len(hdp),
            "matrix_concentration": len(mc),
            "file_walk_universe": len(library),
            "root_modules_separate": len(roots),
            "tmp_scratch": len(tmp),
            "audit_work_scratch": len(audit),
        },
        "hdp": hdp,
        "matrix_concentration": mc,
        "file_walk_universe": library,
        "root_modules_separate": roots,
        "tmp_scratch": tmp,
        "audit_work_scratch": audit,
    }


def render_text(data: dict[str, object], *, include_paths: bool) -> str:
    counts = data["counts"]
    assert isinstance(counts, dict)
    lines = [
        "FILE-WALK UNIVERSE",
        "==================",
        "HDP rule: every .lean physically below HighDimensionalProbability/, excluding Verification/**",
        "MC rule: every .lean physically below the real project-root MatrixConcentration/ directory",
        "Scratch rule: enumerate tmp/*.lean and .audit_work/**/*.lean separately",
        "Always excluded: .lake/** and HighDimensionalProbability/Verification/**",
        "",
    ]
    for key in (
        "hdp",
        "matrix_concentration",
        "file_walk_universe",
        "root_modules_separate",
        "tmp_scratch",
        "audit_work_scratch",
    ):
        lines.append(f"{key}: {counts[key]}")
    if include_paths:
        for key in (
            "hdp",
            "matrix_concentration",
            "file_walk_universe",
            "root_modules_separate",
            "tmp_scratch",
            "audit_work_scratch",
        ):
            lines.extend(("", f"[{key}]"))
            values = data[key]
            assert isinstance(values, list)
            lines.extend(str(value) for value in values)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="emit JSON instead of text")
    parser.add_argument("--paths", action="store_true", help="include every path in text output")
    args = parser.parse_args()
    data = enumerate_universe()
    if args.json:
        print(json.dumps(data, indent=2, sort_keys=True))
    else:
        print(render_text(data, include_paths=args.paths), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
