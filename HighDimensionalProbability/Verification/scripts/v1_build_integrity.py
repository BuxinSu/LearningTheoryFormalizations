#!/usr/bin/env python3
"""Summarize and fail-close the current V1 clean-build evidence."""

from __future__ import annotations

import re
from pathlib import Path

from verify_exercise_reorganization import (
    CERTIFICATE_LOG,
    require_certificate as require_reorganization_certificate,
)

ROOT = Path(__file__).resolve().parents[3]
LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
SOURCE_MANIFEST = LOGS / "source_manifest.txt"
SOURCE_MANIFEST_CHECK = LOGS / "source_manifest_recertification_check.txt"
FULL = LOGS / "build_full_reorganization_clean.log"
APPENDIX = LOGS / "build_appendix_reorganization_clean.log"
FINAL_COPY_MANIFEST = LOGS / "final_clean_copy_manifest_reorganization.log"
FINAL_COPY_BUILDDIR_ABSENCE = (
    LOGS / "final_clean_copy_builddir_absence_reorganization.log"
)
ROUND10_DELTA = LOGS / "round10_docstring_delta.log"

FIELD = re.compile(
    r"^(command|cwd|elapsed_seconds|exit_code):\s*(.*)$", re.MULTILINE
)
ERROR = re.compile(r"(?m)^error:")
SORRY_WARNING = re.compile(
    r"(?m)^warning:.*declaration uses (?:[`'\"])sorry(?:[`'\"])"
)


def fields(path: Path) -> dict[str, str]:
    return dict(FIELD.findall(path.read_text(encoding="utf-8", errors="replace")))


def warning_count(path: Path) -> int:
    return sum(
        line.startswith("warning:")
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines()
    )


def sorry_count(path: Path) -> int:
    return len(
        SORRY_WARNING.findall(path.read_text(encoding="utf-8", errors="replace"))
    )


def error_count(path: Path) -> int:
    return len(ERROR.findall(path.read_text(encoding="utf-8", errors="replace")))


def appendix_import_count() -> int:
    path = ROOT / "HighDimensionalProbability" / "Appendix.lean"
    return sum(
        line.startswith("import HighDimensionalProbability.Appendix.")
        for line in path.read_text(encoding="utf-8").splitlines()
    )


def main() -> int:
    required = (
        SOURCE_MANIFEST,
        SOURCE_MANIFEST_CHECK,
        FULL,
        APPENDIX,
        FINAL_COPY_MANIFEST,
        FINAL_COPY_BUILDDIR_ABSENCE,
        ROUND10_DELTA,
        CERTIFICATE_LOG,
    )
    missing = [path for path in required if not path.is_file()]
    if missing:
        raise FileNotFoundError(", ".join(str(path) for path in missing))

    current_digest = require_reorganization_certificate()
    build_rows = []
    for label, path in (("full", FULL), ("appendix", APPENDIX)):
        metadata = fields(path)
        build_rows.append(
            {
                "label": label,
                "path": path,
                "exit": metadata.get("exit_code", "MISSING"),
                "elapsed": metadata.get("elapsed_seconds", "MISSING"),
                "errors": error_count(path),
                "warnings": warning_count(path),
                "sorries": sorry_count(path),
            }
        )

    summary_text = (
        ROOT
        / "HighDimensionalProbability"
        / "APPENDIX_SUMMARY.md"
    ).read_text(encoding="utf-8")
    full_cwd = fields(FULL).get("cwd", "")
    appendix_cwd = fields(APPENDIX).get("cwd", "")
    final_copy_root = full_cwd if full_cwd == appendix_cwd else "MISMATCH"
    absence_cwd = fields(FINAL_COPY_BUILDDIR_ABSENCE).get("cwd", "")
    manifest_cwd = fields(FINAL_COPY_MANIFEST).get("cwd", "")
    clean_copy_packages = (
        Path(final_copy_root) / ".lake" / "packages"
        if final_copy_root != "MISMATCH"
        else Path("MISMATCH")
    )
    checks = {
        "active_source_manifest_current": (
            current_digest in SOURCE_MANIFEST.read_text(encoding="utf-8")
            and fields(SOURCE_MANIFEST_CHECK).get("exit_code") == "0"
            and "SOURCE MANIFEST OK"
            in SOURCE_MANIFEST_CHECK.read_text(encoding="utf-8")
        ),
        "final_clean_copy_manifest_exit_zero": fields(FINAL_COPY_MANIFEST).get(
            "exit_code"
        ) == "0",
        "final_clean_copy_digest_current": current_digest
        in FINAL_COPY_MANIFEST.read_text(encoding="utf-8"),
        "final_clean_copy_builddir_initially_absent": fields(
            FINAL_COPY_BUILDDIR_ABSENCE
        ).get("exit_code") == "0",
        "clean_copy_provenance_commands_share_root": (
            bool(full_cwd)
            and absence_cwd == full_cwd
            and manifest_cwd == full_cwd
        ),
        "final_builds_run_in_isolated_clean_copy": (
            bool(full_cwd)
            and full_cwd == appendix_cwd
            and Path(full_cwd).is_absolute()
            and Path(full_cwd).resolve() != ROOT.resolve()
        ),
        "clean_copy_uses_pinned_dependency_cache": (
            clean_copy_packages.is_symlink()
            and clean_copy_packages.resolve()
            == (ROOT / ".lake" / "packages").resolve()
        ),
        "round10_docstring_delta_pass": all(
            fragment in ROUND10_DELTA.read_text(encoding="utf-8")
            for fragment in (
                "one_line_docstrings_added: 97",
                "nonblank_nondoc_source_changes: 0",
                "ROUND10_DOCSTRING_DELTA: PASS",
                "exit_code: 0",
            )
        ),
        "exercise_reorganization_delta_pass": all(
            fragment in CERTIFICATE_LOG.read_text(encoding="utf-8")
            for fragment in (
                f"current_digest: {current_digest}",
                "EXERCISE_REORGANIZATION_DELTA: PASS",
                "exit_code: 0",
            )
        ),
        "all_build_exits_zero": all(row["exit"] == "0" for row in build_rows),
        "all_build_error_headers_zero": all(row["errors"] == 0 for row in build_rows),
        "full_sorry_warning_count_228": build_rows[0]["sorries"] == 228,
        "appendix_sorry_warning_count_zero": build_rows[1]["sorries"] == 0,
        "appendix_direct_import_count_15": appendix_import_count() == 15,
        "appendix_summary_active_14_0_0": all(
            fragment in summary_text
            for fragment in (
                "**14/14 source-faithful proved",
                "**RESOLVED BY REMOVAL.**",
                "**835 = 769 core + 66 Appendix + 0",
            )
        ),
    }

    print("V1 CURRENT CLEAN-BUILD SUMMARY")
    print("==============================")
    print(f"clean_absence_command: {fields(FINAL_COPY_BUILDDIR_ABSENCE).get('command')}")
    print(f"clean_absence_exit: {fields(FINAL_COPY_BUILDDIR_ABSENCE).get('exit_code')}")
    print(f"clean_manifest_command: {fields(FINAL_COPY_MANIFEST).get('command')}")
    print(f"clean_manifest_exit: {fields(FINAL_COPY_MANIFEST).get('exit_code')}")
    print(f"final_clean_copy_root: {final_copy_root}")
    print(f"final_clean_copy_source_digest: {current_digest}")
    print()
    print("surface\tlog\texit\telapsed_seconds\terrors\twarnings\tsorry_warnings")
    for row in build_rows:
        print(
            f"{row['label']}\t{row['path'].name}\t{row['exit']}\t"
            f"{row['elapsed']}\t{row['errors']}\t{row['warnings']}\t"
            f"{row['sorries']}"
        )
    print(f"appendix_registry_import_count: {appendix_import_count()}")
    print()
    for name, value in checks.items():
        print(f"{name}: {str(value).lower()}")
    ok = all(checks.values())
    print(f"v1_clean_build_gate: {'PASS' if ok else 'FAIL'}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
