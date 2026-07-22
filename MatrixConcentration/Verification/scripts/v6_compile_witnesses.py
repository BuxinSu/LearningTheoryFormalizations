#!/usr/bin/env python3
"""Compile the V6 positive and deliberately bad witness suites reproducibly.

The single-file Lean driver does not inherit ``leanOptions`` from ``lakefile``;
the required project options are therefore present explicitly in both command
lines.  Combined stdout/stderr and the process exit code are recorded
separately so an empty positive log cannot be mistaken for an unexecuted
command.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
PACKAGE_ROOT = VERIFICATION.parent
REPO_ROOT = PACKAGE_ROOT.parent
LOGS = VERIFICATION / "logs"

LEAN = Path.home() / ".elan" / "bin" / "lake"
COMMON = [
    str(LEAN),
    "env",
    "lean",
    "-DmaxSynthPendingDepth=3",
    "-DrelaxedAutoImplicit=false",
]


def display(command: list[str]) -> str:
    rendered = list(command)
    if rendered and rendered[0] == str(LEAN):
        rendered[0] = "~/.elan/bin/lake"
    return " ".join(rendered)


def compile_one(
    source: str,
    compile_log: Path,
    status_log: Path,
) -> tuple[int, int]:
    command = COMMON + [source]
    process = subprocess.run(
        command,
        cwd=REPO_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    compile_log.write_bytes(process.stdout)
    status_log.write_text(
        "\n".join(
            [
                f"command: {display(command)}",
                f"exit_code: {process.returncode}",
                f"stdout_stderr_bytes: {len(process.stdout)}",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return process.returncode, len(process.stdout)


def main() -> int:
    LOGS.mkdir(parents=True, exist_ok=True)
    good_code, good_bytes = compile_one(
        "MatrixConcentration/Verification/scripts/witnesses/V6Witnesses.lean",
        LOGS / "v6_witnesses_compile.log",
        LOGS / "v6_witnesses_compile_status.log",
    )
    bad_code, bad_bytes = compile_one(
        ".audit_work/BadWitness.lean",
        LOGS / "calibration_bad_witness_compile.log",
        LOGS / "calibration_bad_witness_compile_status.log",
    )
    lines = [
        "V6 WITNESS COMPILATION",
        f"OFFICIAL_EXIT_CODE {good_code}",
        f"OFFICIAL_OUTPUT_BYTES {good_bytes}",
        f"BAD_CALIBRATION_EXIT_CODE {bad_code}",
        f"BAD_CALIBRATION_OUTPUT_BYTES {bad_bytes}",
        "NOTE the bad calibration is expected to compile with a `sorry` warning; "
        "v6_check_witnesses.py must reject that warning.",
    ]
    print("\n".join(lines))
    return 0 if good_code == 0 and bad_code == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
