"""Book, policy-selection, toolchain, and service configuration models."""

from pathlib import Path
from typing import Literal

from pydantic import BaseModel, Field, field_serializer, model_validator


class ServiceConfig(BaseModel):
    protocol: Literal["openai_responses", "generic_json", "codex_cli"] = "openai_responses"
    endpoint: str
    model: str | None = None
    api_key_env: str
    timeout_seconds: int = 900


class CodexConfig(BaseModel):
    executable: str = "codex"
    sandbox: Literal["read-only", "workspace-write"] = "workspace-write"
    timeout_seconds: int = 21600
    draft_model: str | None = None
    revision_model: str | None = None


class SourceConfig(BaseModel):
    prefer_authoritative: bool = True
    authoritative_url: str | None = None
    pdf_is_final_authority: bool = True
    chapter_detection: Literal["auto", "latex"] = "auto"


class LeanConfig(BaseModel):
    toolchain: str
    mathlib_revision: str
    project_name: str
    namespace: str


class ChapterConfig(BaseModel):
    order: list[str] | Literal["auto"] = "auto"
    starts_at: int = 1


class PromptConfig(BaseModel):
    formalization_policy: Path
    source_conventions: Path
    draft_template: Path
    review_template: Path
    revision_template: Path


class PolicyConfig(BaseModel):
    """Profile-selected workflow policy; all paths are resolved before agents run."""

    profile_name: str = "default"
    profile_version: str = "1"
    authoritative_page_start: int | None = Field(default=None, ge=1)
    authoritative_page_end: int | None = Field(default=None, ge=1)
    transcription_status: Literal["not_started", "partial", "complete", "verified"] = (
        "not_started"
    )
    required_paths: list[Path] = Field(default_factory=list)
    exercise_paths: list[Path] = Field(default_factory=list)
    hint_paths: list[Path] = Field(default_factory=list)
    report_paths: list[Path] = Field(default_factory=list)
    module_layout: dict[str, str] = Field(default_factory=dict)
    allowed_gap_categories: set[Literal["A", "B", "C", "D"]] = Field(
        default_factory=lambda: {"A", "B", "C", "D"}
    )
    allow_human_waivers: bool = True
    pass_budgets: dict[str, int] = Field(
        default_factory=lambda: {"formalization": 6, "proofread": 2, "correction": 6}
    )

    @field_serializer("allowed_gap_categories")
    def serialize_gap_categories(self, value: set[str]) -> list[str]:
        return sorted(value)


class BookConfig(BaseModel):
    book_id: str = Field(pattern=r"^[a-z0-9][a-z0-9-]*$")
    title: str
    authors: list[str] = Field(default_factory=list)
    input_pdf: Path
    source: SourceConfig
    lean: LeanConfig
    chapters: ChapterConfig = Field(default_factory=ChapterConfig)
    prompts: PromptConfig
    policy: PolicyConfig = Field(default_factory=PolicyConfig)
    runtime_dir: Path = Path(".autoformal")
    output_dir: Path = Path("output")
    revision_limit: int = Field(default=3, ge=0, le=20)
    transport_retries: int = Field(default=3, ge=0, le=10)
    codex: CodexConfig
    reviewer: ServiceConfig
    converter: ServiceConfig

    @model_validator(mode="after")
    def validate_models(self) -> "BookConfig":
        if self.reviewer.protocol != "codex_cli" and not self.reviewer.model:
            raise ValueError("reviewer.model must be configured for HTTP reviewers")
        start = self.policy.authoritative_page_start
        end = self.policy.authoritative_page_end
        if start is not None and end is not None and start > end:
            raise ValueError("authoritative_page_start must not exceed authoritative_page_end")
        return self
