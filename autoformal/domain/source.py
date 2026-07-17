"""Authoritative source, inventory, and source-claim models."""

from datetime import datetime
from typing import Literal

from pydantic import BaseModel, Field

from .enums import CoverageDecision, CoverageStatus


class ValidationCheck(BaseModel):
    name: str
    passed: bool
    details: str


class SectionRecord(BaseModel):
    id: str
    title: str
    tex_path: str
    page_start: int | None = None
    page_end: int | None = None


class ChapterRecord(BaseModel):
    id: str
    title: str
    tex_path: str
    page_start: int | None = None
    page_end: int | None = None
    sections: list[SectionRecord] = Field(default_factory=list)


class SourceManifest(BaseModel):
    book_id: str
    pdf_path: str
    pdf_sha256: str
    page_count: int | None = None
    provenance: Literal["authoritative_tex", "ai_conversion"]
    canonical_tex_root: str
    chapters: list[ChapterRecord]
    validation: list[ValidationCheck]
    approved_by: str | None = None
    approved_at: datetime | None = None


AuditKind = Literal[
    "definition",
    "named_result",
    "numbered_equation",
    "display",
    "prose_claim",
    "negative_claim",
    "footnote",
    "hidden_obligation",
    "exercise",
    "example",
]


class SourceClaim(BaseModel):
    id: str
    book_id: str
    chapter_id: str | None = None
    section_id: str | None = None
    kind: AuditKind | Literal["historical", "bibliographic", "motivational", "external_result"]
    claim: str
    pdf_location: str
    tex_location: str | None = None
    later_uses: list[str] = Field(default_factory=list)
    load_bearing: bool = False
    external_used_downstream: bool = False
    exercise_is_proof_question: bool | None = None
    decision: CoverageDecision = CoverageDecision.FORMALIZE
    coverage_status: CoverageStatus = CoverageStatus.MISSING
    lean_declarations: list[str] = Field(default_factory=list)
    evidence_hash: str | None = None
