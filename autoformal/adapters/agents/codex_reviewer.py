from __future__ import annotations

import subprocess
from datetime import datetime, timezone
from pathlib import Path

from ...artifacts import atomic_write_text
from ...domain import CodexConfig, CommandResult, ReviewerResult, ServiceConfig
from .codex_cli import CodexCLI, CodexExecutionError


class CodexReviewer:
    """Independent, read-only Codex session used as the mathematical reviewer."""

    def __init__(self, codex: CodexConfig, reviewer: ServiceConfig, schema_path: Path) -> None:
        self.codex = codex
        self.reviewer = reviewer
        self.schema_path = schema_path

    def review(
        self,
        prompt: str,
        worktree: Path,
        events_path: Path,
        last_message_path: Path,
    ) -> tuple[ReviewerResult, str | None, CommandResult]:
        events_path.parent.mkdir(parents=True, exist_ok=True)
        last_message_path.parent.mkdir(parents=True, exist_ok=True)
        command = [
            self.codex.executable, "exec", "--json",
            "--output-schema", str(self.schema_path),
            "--output-last-message", str(last_message_path),
            "--cd", str(worktree), "--sandbox", "read-only",
        ]
        if self.reviewer.model:
            command.extend(["--model", self.reviewer.model])
        command.append("-")
        started = datetime.now(timezone.utc)
        try:
            completed = subprocess.run(
                command, cwd=worktree, input=prompt, text=True, capture_output=True,
                timeout=self.reviewer.timeout_seconds, check=False,
            )
        except subprocess.TimeoutExpired as error:
            result = CommandResult(
                command=command, returncode=124, stdout=error.stdout or "",
                stderr=error.stderr or "timeout", started_at=started,
                finished_at=datetime.now(timezone.utc),
            )
            raise CodexExecutionError("Codex reviewer timed out", result) from error
        atomic_write_text(events_path, completed.stdout)
        result = CommandResult(
            command=command, returncode=completed.returncode, stdout=completed.stdout,
            stderr=completed.stderr, started_at=started,
            finished_at=datetime.now(timezone.utc),
        )
        if completed.returncode != 0:
            raise CodexExecutionError(
                f"Codex reviewer exited with status {completed.returncode}", result
            )
        try:
            review = ReviewerResult.model_validate_json(last_message_path.read_text(encoding="utf-8"))
        except Exception as error:
            raise CodexExecutionError(
                "Codex reviewer response did not match ReviewerResult schema", result
            ) from error
        return review, CodexCLI._session_id(completed.stdout), result
