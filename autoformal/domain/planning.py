"""Resolved policy, preflight, theorem-contract, and formalization-plan models."""

from datetime import datetime
from typing import Literal

from pydantic import BaseModel, Field, computed_field, field_serializer

from .common import utc_now
from .source import ValidationCheck


class PolicyProfile(BaseModel):
    book_id: str
    name: str
    version: str
    pdf_is_final_authority: bool = True
    source_authority_rules: list[str] = Field(default_factory=list)
    allowed_gap_categories: set[Literal["A", "B", "C", "D"]]
    module_layout: dict[str, str] = Field(default_factory=dict)
    required_paths: list[str] = Field(default_factory=list)
    pass_budgets: dict[str, int] = Field(default_factory=dict)
    policy_hash: str
    resolved_at: datetime = Field(default_factory=utc_now)

    @field_serializer("allowed_gap_categories")
    def serialize_gap_categories(self, value: set[str]) -> list[str]:
        return sorted(value)


class PreflightManifest(BaseModel):
    book_id: str
    policy_hash: str
    checks: list[ValidationCheck]
    resolved_paths: dict[str, str] = Field(default_factory=dict)
    toolchain: str
    mathlib_revision: str
    source_page_range: tuple[int | None, int | None] = (None, None)
    transcription_status: str
    build_hash: str | None = None
    created_at: datetime = Field(default_factory=utc_now)

    @computed_field
    @property
    def passed(self) -> bool:
        return all(check.passed for check in self.checks)


class TheoremContract(BaseModel):
    declaration: str
    lean_type: str
    source_claim_id: str | None = None
    chapter_id: str | None = None
    public: bool = True
    required: bool = True


class FormalizationPlan(BaseModel):
    id: str
    book_id: str
    policy_hash: str
    theorem_contracts: list[TheoremContract] = Field(default_factory=list)
    load_bearing_claim_ids: list[str] = Field(default_factory=list)
    memory_declaration_ids: list[str] = Field(default_factory=list)
    module_dag: dict[str, list[str]] = Field(default_factory=dict)
    core_modules: list[str] = Field(default_factory=list)
    exercise_modules: list[str] = Field(default_factory=list)
    appendix_modules: list[str] = Field(default_factory=list)
    deferred_modules: list[str] = Field(default_factory=list)
    obligation_ids: list[str] = Field(default_factory=list)
    verification_commands: list[list[str]] = Field(default_factory=list)
    acceptance_conditions: list[str] = Field(default_factory=list)
    approved_by: str | None = None
    approved_at: datetime | None = None
    created_at: datetime = Field(default_factory=utc_now)
