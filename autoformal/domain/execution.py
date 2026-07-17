"""Agent execution, command evidence, jobs, leases, and review-run models."""

from datetime import datetime
from typing import Any, Literal

from pydantic import BaseModel, Field

from .common import utc_now


class AgentResult(BaseModel):
    status: Literal["completed", "blocked", "failed"]
    summary: str
    files_changed: list[str] = Field(default_factory=list)
    checks: list[str] = Field(default_factory=list)
    unresolved_issues: list[str] = Field(default_factory=list)
    checkpoint: str | None = None


class CommandResult(BaseModel):
    command: list[str]
    returncode: int
    stdout: str
    stderr: str
    started_at: datetime
    finished_at: datetime
    metadata: dict[str, Any] = Field(default_factory=dict)


class AgentJob(BaseModel):
    id: str
    book_id: str
    chapter_id: str | None = None
    role: Literal["formalizer", "proofreader", "corrector", "appendix", "planner", "preflight"]
    pass_name: str
    allowed_paths: list[str] = Field(default_factory=list)
    read_only: bool = False
    input_snapshot_hash: str
    checkpoint: str | None = None
    status: Literal["queued", "running", "completed", "blocked", "failed"] = "queued"
    session_id: str | None = None
    latest_attempt_id: str | None = None
    last_green_attempt_id: str | None = None
    created_at: datetime = Field(default_factory=utc_now)
    updated_at: datetime = Field(default_factory=utc_now)


class PathLease(BaseModel):
    id: str
    book_id: str
    job_id: str
    scope: Literal["core", "chapter", "appendix", "report"]
    path: str
    acquired_at: datetime = Field(default_factory=utc_now)
    expires_at: datetime
    released_at: datetime | None = None


class ReviewRun(BaseModel):
    id: str
    book_id: str
    chapter_id: str | None = None
    input_manifest: dict[str, str]
    semantic_fingerprint: str
    status: Literal["running", "complete", "archived"] = "running"
    coverage_counts: dict[str, int] = Field(default_factory=dict)
    created_at: datetime = Field(default_factory=utc_now)
    completed_at: datetime | None = None
