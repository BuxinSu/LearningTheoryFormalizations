#!/usr/bin/env python3
"""Compile the importable witness module and dynamic Tier-C evidence harness."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
PACKAGE_ROOT = VERIFICATION.parent
REPO_ROOT = PACKAGE_ROOT.parent
LOGS = VERIFICATION / "logs"
LAKE = Path.home() / ".elan" / "bin" / "lake"


def run(
    command: list[str],
    compile_log: Path,
    status_log: Path,
) -> int:
    result = subprocess.run(
        command,
        cwd=REPO_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    compile_log.write_bytes(result.stdout)
    rendered = " ".join(
        ["~/.elan/bin/lake" if item == str(LAKE) else item for item in command]
    )
    status_log.write_text(
        f"command: {rendered}\n"
        f"exit_code: {result.returncode}\n"
        f"stdout_stderr_bytes: {len(result.stdout)}\n",
        encoding="utf-8",
    )
    return result.returncode


def main() -> int:
    LOGS.mkdir(parents=True, exist_ok=True)
    module_code = run(
        [
            str(LAKE),
            "build",
            "MatrixConcentration.Verification.scripts.witnesses.V6Witnesses",
        ],
        LOGS / "v6_witness_module_build.log",
        LOGS / "v6_witness_module_build_status.log",
    )
    evidence_code = 1
    if module_code == 0:
        evidence_code = run(
            [
                str(LAKE),
                "env",
                "lean",
                "-DmaxSynthPendingDepth=3",
                "-DrelaxedAutoImplicit=false",
                "MatrixConcentration/Verification/scripts/"
                "v6_tier_c_environment_evidence.lean",
            ],
            LOGS / "v6_tier_c_environment_compile.log",
            LOGS / "v6_tier_c_environment_compile_status.log",
        )
    print("V6 TIER-C ENVIRONMENT EVIDENCE COMPILATION")
    print(f"WITNESS_MODULE_EXIT_CODE {module_code}")
    print(f"EVIDENCE_HARNESS_EXIT_CODE {evidence_code}")
    return 0 if module_code == 0 and evidence_code == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
