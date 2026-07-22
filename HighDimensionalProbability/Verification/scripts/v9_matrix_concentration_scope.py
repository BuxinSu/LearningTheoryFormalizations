#!/usr/bin/env python3
"""Measure the current vendored MatrixConcentration publication-record scope."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
MC = ROOT / "MatrixConcentration"
RECORD_SUFFIXES = {".md", ".txt", ".json", ".tsv", ".csv"}


def main() -> int:
    modules = sorted(path for path in MC.rglob("*.lean") if path.is_file())
    records = sorted(
        path
        for path in MC.rglob("*")
        if path.is_file() and path.suffix.lower() in RECORD_SUFFIXES
    )
    nested_symlinks = sorted(path for path in MC.rglob("*") if path.is_symlink())
    upstream = ROOT.parent / "MatrixConcentration"
    checks = {
        "vendored_real_directory": MC.is_dir() and not MC.is_symlink(),
        "vendored_module_count_10": len(modules) == 10,
        "vendored_record_count_0": not records,
        "vendored_nested_symlink_count_0": not nested_symlinks,
        "pre_matrix_concentration_absent": not (
            (ROOT / "Pre_MatrixConcentration").exists()
            or (ROOT / "Pre_MatrixConcentration").is_symlink()
        ),
        "matrix_root_module_absent": not (ROOT / "MatrixConcentration.lean").exists(),
        "freestanding_upstream_exists_outside_project": (
            upstream.is_dir() and upstream.resolve() != MC.resolve()
        ),
    }
    print("V9 MATRIXCONCENTRATION RECORD-SCOPE CENSUS")
    print("==========================================")
    print(f"project_root: {ROOT}")
    print(f"vendored_path: {MC.relative_to(ROOT)}")
    print(f"vendored_modules: {len(modules)}")
    for path in modules:
        print(f"MODULE\t{path.relative_to(ROOT).as_posix()}")
    print(f"vendored_record_files: {len(records)}")
    for path in records:
        print(f"RECORD\t{path.relative_to(ROOT).as_posix()}")
    print(f"vendored_nested_symlinks: {len(nested_symlinks)}")
    print(f"freestanding_upstream_path: {upstream}")
    print("freestanding_upstream_policy: OUT-OF-SCOPE; never scanned for claims")
    for name, value in checks.items():
        print(f"{name}: {str(value).lower()}")
    ok = all(checks.values())
    print(f"scope_gate: {'PASS' if ok else 'FAIL'}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
