from __future__ import annotations

import subprocess
from datetime import datetime, timezone
from pathlib import Path

from ...domain import CommandResult


def run_command(command: list[str], cwd: Path, timeout: int = 3600) -> CommandResult:
    started = datetime.now(timezone.utc)
    try:
        completed = subprocess.run(command, cwd=cwd, text=True, capture_output=True, timeout=timeout, check=False)
        return CommandResult(
            command=command, returncode=completed.returncode, stdout=completed.stdout, stderr=completed.stderr,
            started_at=started, finished_at=datetime.now(timezone.utc),
        )
    except subprocess.TimeoutExpired as error:
        return CommandResult(
            command=command, returncode=124, stdout=error.stdout or "", stderr=error.stderr or "timeout",
            started_at=started, finished_at=datetime.now(timezone.utc),
        )


def lake_build(project: Path, timeout: int = 7200) -> CommandResult:
    return run_command(["lake", "build"], project, timeout)


def lean_version(project: Path) -> CommandResult:
    return run_command(["lake", "env", "lean", "--version"], project, 60)

