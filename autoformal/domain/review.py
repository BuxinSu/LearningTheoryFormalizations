"""Coverage inventory, reviewer, verdict, and human-evidence models."""

from datetime import datetime
from typing import Literal

from pydantic import BaseModel, Field, model_validator

from .common import utc_now
from .source import AuditKind


class AuditUnit(BaseModel):
    id: str
    section_id: str
    kind: AuditKind
    source_location: str
    claim: str
    assumptions: list[str] = Field(default_factory=list)
    decision: Literal["formalize", "defer", "omit", "source_issue"] = "formalize"
    omission_reason: str | None = None
    lean_declarations: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def omission_has_reason(self) -> "AuditUnit":
        if self.decision in {"omit", "source_issue"} and not self.omission_reason:
            raise ValueError("omitted/source-issue audit units require omission_reason")
        return self


class AuditInventory(BaseModel):
    book_id: str
    chapter_id: str
    units: list[AuditUnit]


class ReviewerFinding(BaseModel):
    id: str
    audit_unit_id: str | None = None
    severity: Literal["blocker", "warning", "info"]
    category: Literal[
        "missing_content",
        "statement_mismatch",
        "assumption_mismatch",
        "proof_gap",
        "formatting",
        "source_reference",
        "source_issue",
        "coverage_uncertain",
    ]
    source_location: str
    lean_location: str | None = None
    difference: str
    evidence: str
    required_fix: str


class AuditResult(BaseModel):
    audit_unit_id: str
    coverage: Literal[
        "exact",
        "equivalent",
        "stronger_accepted",
        "weaker",
        "partial",
        "incomparable",
        "missing",
        "justified_omission",
        "source_issue",
        "unable_to_verify",
    ]
    proof_status: Literal[
        "complete", "incomplete", "axiomatic", "not_applicable", "unable_to_verify"
    ]
    notes: str


class ReviewerResult(BaseModel):
    assessment: Literal[
        "complete_and_accurate",
        "complete_with_stronger_formulations",
        "substantially_complete_with_issues",
        "incomplete_or_inaccurate",
    ]
    audit_results: list[AuditResult]
    findings: list[ReviewerFinding]
    markdown_report: str

    @property
    def blockers(self) -> list[ReviewerFinding]:
        return [finding for finding in self.findings if finding.severity == "blocker"]


class ChapterVerdict(BaseModel):
    book_id: str
    chapter_id: str
    classification: Literal[
        "fully_formalized_and_verified",
        "main_line_verified_deferred_items",
        "main_line_verified_deferred_leaf_items",
        "structurally_complete_conditionally_verified",
        "incomplete",
    ]
    build_passed: bool
    blocking_findings: int = Field(ge=0)
    counts: dict[str, int] = Field(default_factory=dict)
    artifact_hashes: dict[str, str] = Field(default_factory=dict)


class HumanDecision(BaseModel):
    audit_unit_id: str
    decision: Literal["approved", "rejected"]
    approver: str
    decided_at: datetime = Field(default_factory=utc_now)
    source_hash: str
    lean_hash: str
    notes: str = ""
    evidence_hashes: dict[str, str] = Field(default_factory=dict)


class FindingValidation(BaseModel):
    id: str
    finding_id: str
    review_run_id: str
    disposition: Literal["confirmed", "rejected", "revised"]
    pdf_evidence: str
    lean_evidence: str
    revised_difference: str | None = None
    validator: str
    created_at: datetime = Field(default_factory=utc_now)

    @model_validator(mode="after")
    def revised_has_difference(self) -> "FindingValidation":
        if self.disposition == "revised" and not self.revised_difference:
            raise ValueError("revised finding validation requires revised_difference")
        return self
