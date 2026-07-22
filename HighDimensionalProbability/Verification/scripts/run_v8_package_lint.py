#!/usr/bin/env python3
"""Run the deferred V8 package lint and normalize its expected exit behavior.

This file is infrastructure only until V7 is complete.  The ``run`` action
requires an explicit sequencing acknowledgement.  A raw Lean exit code of one
is normal when ``#lint`` reports hits; the preserved log is parsed and gated
before this wrapper decides whether the run itself was structurally valid.

The current harness imports the full physical surface: the HDP root, isolated
Appendix closure, and all ten modules selected by the MatrixConcentration
lakefile glob.
"""

from __future__ import annotations

import argparse
import json
import shlex
import subprocess
import sys
from pathlib import Path
from typing import Sequence

from file_universe import ROOT
from lean_source_scanner import mask_lean_noncode
from v8_lint_parser import (
    DEFAULT_MIN_DECLARATIONS,
    EXPECTED_PACKAGES,
    FAILED_ORPHAN_MODULES,
    FULL_SURFACE_HARNESS_REL,
    MAXIMAL_HARNESS_REL,
    REQUIRED_D_FLAGS,
    parse_lint_log,
    report_dict,
)


HARNESS = ROOT / MAXIMAL_HARNESS_REL
FULL_SURFACE_HARNESS = ROOT / FULL_SURFACE_HARNESS_REL
RUN_LOGGED = (
    ROOT
    / "HighDimensionalProbability"
    / "Verification"
    / "scripts"
    / "run_logged.py"
)
DEFAULT_LOG = (
    ROOT
    / "HighDimensionalProbability"
    / "Verification"
    / "logs"
    / "recert_v8_package_lint.log"
)
DEFAULT_REPORT = (
    ROOT
    / "HighDimensionalProbability"
    / "Verification"
    / "logs"
    / "recert_v8_package_lint.json"
)
DEFAULT_FULL_SURFACE_LOG = (
    ROOT
    / "HighDimensionalProbability"
    / "Verification"
    / "logs"
    / "recert_v8_package_lint.log"
)
DEFAULT_FULL_SURFACE_REPORT = (
    ROOT
    / "HighDimensionalProbability"
    / "Verification"
    / "logs"
    / "recert_v8_package_lint.json"
)
V2_ORPHAN_SUMMARY = (
    ROOT
    / "HighDimensionalProbability"
    / "Verification"
    / "logs"
    / "v2_orphan_recertification_summary.log"
)
REQUIRED_IMPORTS = (
    "HighDimensionalProbability",
    "HighDimensionalProbability.Appendix",
    "MatrixConcentration.Prelude",
    "MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices",
    "MatrixConcentration.Chapter3_MatrixLaplaceTransformMethod",
    "MatrixConcentration.Chapter4_MatrixGaussianAndRademacherSeries",
    "MatrixConcentration.Chapter5_SumOfPSDMatrices",
    "MatrixConcentration.Chapter8_ProofOfLiebsTheorem",
    "MatrixConcentration.Appendix_GoldenThompson",
    "MatrixConcentration.Appendix_GaussianConcentration",
    "MatrixConcentration.Appendix_SymmetricLowerBound",
    "MatrixConcentration.Appendix_MatrixRosenthal",
)
FAILED_ORPHAN_IMPORTS = FAILED_ORPHAN_MODULES
FULL_SURFACE_IMPORTS = REQUIRED_IMPORTS
EXPECTED_V2_BUILD_EXIT: dict[str, int] = {}


def _expected_imports(path: Path) -> tuple[str, ...]:
    if path.resolve() == FULL_SURFACE_HARNESS.resolve():
        return FULL_SURFACE_IMPORTS
    return REQUIRED_IMPORTS


def validate_harness(path: Path = HARNESS) -> list[str]:
    diagnostics: list[str] = []
    if path.is_symlink() or not path.is_file():
        return [f"harness is not a physical regular file: {path}"]
    text = path.read_text(encoding="utf-8")
    code, lexical_diagnostics = mask_lean_noncode(text)
    if lexical_diagnostics:
        diagnostics.append(
            "harness has lexical diagnostics: "
            + ", ".join(kind for kind, _ in lexical_diagnostics)
        )

    imports: list[str] = []
    lint_commands: list[str] = []
    for line in code.splitlines():
        stripped = line.strip()
        if stripped.startswith("import "):
            imports.extend(stripped[len("import ") :].split())
        if stripped.startswith("#lint"):
            lint_commands.append(" ".join(stripped.split()))

    expected_imports = _expected_imports(path)
    if imports != list(expected_imports):
        diagnostics.append(
            f"harness imports are {imports!r}; expected exact surface "
            f"{list(expected_imports)!r}"
        )
    expected_commands = [f"#lint in {package}" for package in EXPECTED_PACKAGES]
    if lint_commands != expected_commands:
        diagnostics.append(
            f"harness lint commands are {lint_commands!r}; expected exactly "
            f"{expected_commands!r}"
        )
    return diagnostics


def validate_all_harnesses() -> list[str]:
    return [
        *(f"maximal-buildable: {item}" for item in validate_harness(HARNESS)),
        *(
            f"full-surface gate: {item}"
            for item in validate_harness(FULL_SURFACE_HARNESS)
        ),
    ]


def validate_v2_orphan_evidence(
    path: Path = V2_ORPHAN_SUMMARY,
) -> list[str]:
    if path.is_symlink() or not path.is_file():
        return [f"V2 orphan summary is not a physical regular file: {path}"]
    rows: dict[str, int] = {}
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        fields = line.split("\t")
        if len(fields) < 5 or fields[0] not in EXPECTED_V2_BUILD_EXIT:
            continue
        try:
            rows[fields[0]] = int(fields[4])
        except ValueError:
            return [f"V2 orphan build exit is not numeric: {line!r}"]
    diagnostics = []
    if rows != EXPECTED_V2_BUILD_EXIT:
        diagnostics.append(
            "V2 orphan build evidence changed: "
            f"expected {EXPECTED_V2_BUILD_EXIT!r}, observed {rows!r}"
        )
    return diagnostics


def build_lean_command(path: Path = HARNESS) -> list[str]:
    relative = path.relative_to(ROOT).as_posix()
    return [
        "lake",
        "env",
        "lean",
        *REQUIRED_D_FLAGS,
        relative,
    ]


def _root_path(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def run(
    *,
    harness: Path,
    log_path: Path,
    report_path: Path,
    minimum_declarations_per_package: int,
    fail_on_lint_hits: bool,
) -> int:
    harness_diagnostics = validate_all_harnesses()
    harness_diagnostics.extend(validate_v2_orphan_evidence())
    if harness_diagnostics:
        for diagnostic in harness_diagnostics:
            print(f"V8 harness error: {diagnostic}", file=sys.stderr)
        return 2

    log_path = _root_path(log_path)
    report_path = _root_path(report_path)
    command = build_lean_command(harness)
    logged_command = [
        sys.executable,
        str(RUN_LOGGED),
        "--log",
        str(log_path),
        "--",
        *command,
    ]
    print("V8 raw command:", shlex.join(command))
    completed = subprocess.run(logged_command, cwd=ROOT, check=False)

    if not log_path.is_file():
        print(f"V8 log was not created: {log_path}", file=sys.stderr)
        return 2
    report = parse_lint_log(
        log_path.read_text(encoding="utf-8", errors="replace"),
        log_path=(
            log_path.relative_to(ROOT).as_posix()
            if log_path.is_relative_to(ROOT)
            else str(log_path)
        ),
        minimum_declarations_per_package=minimum_declarations_per_package,
        require_run_metadata=True,
    )
    if report.exit_code != completed.returncode:
        report.diagnostics.append(
            f"run_logged returned {completed.returncode}, but its footer "
            f"records {report.exit_code}"
        )
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = report_dict(report)
    payload.update(
        {
            "included_buildable_orphan_modules": [],
            "explicit_reachable_appendix_dependency_modules": [],
            "v2_orphan_evidence": (
                V2_ORPHAN_SUMMARY.relative_to(ROOT).as_posix()
            ),
            "full_surface_gate_required_for_complete_status": False,
        }
    )
    report_path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    print(f"V8 raw Lean exit code: {completed.returncode}")
    print(f"V8 reported lint hits: {report.total_errors}")
    print(f"V8 parsed lint hits: {report.total_hits}")
    print(f"V8 surface profile: {report.surface_profile}")
    print(f"V8 coverage status: {report.coverage_status}")
    print(f"V8 overall status: {report.overall_status}")
    print(f"V8 report: {report_path}")
    if not report.gate_passed:
        for diagnostic in report.diagnostics:
            print(f"V8 gate error: {diagnostic}", file=sys.stderr)
        return 2
    if not report.coverage_complete:
        print("V8 coverage gate did not recognize the full current surface", file=sys.stderr)
        return 2
    if fail_on_lint_hits and report.total_errors:
        return 1
    print(
        "V8 structural gate passed; a nonzero raw Lean exit was expected"
        if report.total_errors
        else "V8 structural gate passed with no lint hits"
    )
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Run/log V8 only after the V7 evidence pass is complete"
    )
    parser.add_argument(
        "--confirm-v7-complete",
        action="store_true",
        help="required sequencing acknowledgement before Lean is invoked",
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument(
        "--full-surface-gate",
        action="store_true",
        help=(
            "accepted for compatibility; the default harness already is the "
            "complete current physical surface"
        ),
    )
    parser.add_argument("--log", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument(
        "--minimum-declarations-per-package",
        type=int,
        default=DEFAULT_MIN_DECLARATIONS,
    )
    parser.add_argument(
        "--fail-on-lint-hits",
        action="store_true",
        help="after structural validation, return one when lint hits exist",
    )
    args = parser.parse_args(argv)

    diagnostics = validate_all_harnesses()
    diagnostics.extend(validate_v2_orphan_evidence())
    if diagnostics:
        for diagnostic in diagnostics:
            print(f"V8 harness error: {diagnostic}", file=sys.stderr)
        return 2
    if args.dry_run:
        selected_harness = (
            FULL_SURFACE_HARNESS if args.full_surface_gate else HARNESS
        )
        print(shlex.join(build_lean_command(selected_harness)))
        return 0
    if not args.confirm_v7_complete:
        parser.error(
            "--confirm-v7-complete is required; V8 must not run before V7"
        )
    harness = FULL_SURFACE_HARNESS if args.full_surface_gate else HARNESS
    log_path = args.log or (
        DEFAULT_FULL_SURFACE_LOG if args.full_surface_gate else DEFAULT_LOG
    )
    report_path = args.report or (
        DEFAULT_FULL_SURFACE_REPORT
        if args.full_surface_gate
        else DEFAULT_REPORT
    )
    return run(
        harness=harness,
        log_path=log_path,
        report_path=report_path,
        minimum_declarations_per_package=(
            args.minimum_declarations_per_package
        ),
        fail_on_lint_hits=args.fail_on_lint_hits,
    )


if __name__ == "__main__":
    raise SystemExit(main())
