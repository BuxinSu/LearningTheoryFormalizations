"""Structural ports used by the shared verification service."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Protocol

from ...domain import CommandResult, ProofObligation


class ArtifactWriter(Protocol):
    def path(self, *parts: str) -> Path: ...
    def write_json(self, relative: str, value: Any) -> Path: ...


class GreenWorkspace(Protocol):
    path: Path

    def commit_green(self, message: str) -> str: ...


class VerificationState(Protocol):
    def obligations(self, book_id: str, chapter_id: str | None = None) -> list[ProofObligation]: ...
    def create_attempt(
        self,
        job_id: str,
        status: str,
        *,
        session_id: str | None = None,
        checkpoint: str | None = None,
        green_commit: str | None = None,
        payload: dict[str, Any] | None = None,
    ) -> str: ...
