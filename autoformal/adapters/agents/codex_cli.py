from __future__ import annotations

import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from ...artifacts import atomic_write_text
from ...domain import AgentResult, CodexConfig, CommandResult


class CodexExecutionError(RuntimeError):
    def __init__(self, message: str, result: CommandResult) -> None:
        super().__init__(message)
        self.result = result


class CodexCLI:
    def __init__(self, config: CodexConfig) -> None:
        self.config = config

    def run(
        self,
        prompt: str,
        worktree: Path,
        schema_path: Path,
        events_path: Path,
        last_message_path: Path,
        model: str | None = None,
        session_id: str | None = None,
    ) -> tuple[AgentResult, str | None, CommandResult]:
        events_path.parent.mkdir(parents=True, exist_ok=True)
        last_message_path.parent.mkdir(parents=True, exist_ok=True)
        if session_id:
            command = [self.config.executable, "exec", "resume", "--json", "--output-schema", str(schema_path)]
            if model:
                command.extend(["--model", model])
            command.extend(["--output-last-message", str(last_message_path), session_id, "-"])
        else:
            command = [
                self.config.executable, "exec", "--json", "--output-schema", str(schema_path),
                "--output-last-message", str(last_message_path), "--cd", str(worktree),
                "--sandbox", self.config.sandbox,
            ]
            if model:
                command.extend(["--model", model])
            command.append("-")

        started = datetime.now(timezone.utc)
        try:
            completed = subprocess.run(
                command, cwd=worktree, input=prompt, text=True, capture_output=True,
                timeout=self.config.timeout_seconds, check=False,
            )
        except subprocess.TimeoutExpired as error:
            result = CommandResult(
                command=command, returncode=124, stdout=error.stdout or "", stderr=error.stderr or "timeout",
                started_at=started, finished_at=datetime.now(timezone.utc),
            )
            raise CodexExecutionError("Codex execution timed out", result) from error

        atomic_write_text(events_path, completed.stdout)
        result = CommandResult(
            command=command, returncode=completed.returncode, stdout=completed.stdout, stderr=completed.stderr,
            started_at=started, finished_at=datetime.now(timezone.utc),
        )
        if completed.returncode != 0:
            raise CodexExecutionError(f"Codex exited with status {completed.returncode}", result)
        try:
            agent_result = AgentResult.model_validate_json(last_message_path.read_text(encoding="utf-8"))
        except Exception as error:
            raise CodexExecutionError("Codex final response did not match AgentResult schema", result) from error
        return agent_result, self._session_id(completed.stdout), result

    @staticmethod
    def _session_id(jsonl: str) -> str | None:
        preferred = ("thread_id", "session_id", "conversation_id")
        for line in jsonl.splitlines():
            try:
                payload = json.loads(line)
            except json.JSONDecodeError:
                continue
            stack: list[Any] = [payload]
            while stack:
                current = stack.pop()
                if isinstance(current, dict):
                    for key in preferred:
                        if isinstance(current.get(key), str):
                            return current[key]
                    stack.extend(current.values())
                elif isinstance(current, list):
                    stack.extend(current)
        return None

