"""Tracked proof-obligation model and taxonomy validation."""

from datetime import datetime

from pydantic import BaseModel, Field, model_validator

from .common import utc_now
from .enums import ObligationKind, ObligationStatus


class ProofObligation(BaseModel):
    id: str
    book_id: str
    chapter_id: str | None = None
    kind: ObligationKind
    status: ObligationStatus = ObligationStatus.OPEN
    declaration: str | None = None
    source_claim_id: str | None = None
    source_evidence: str
    reason: str
    attempted_routes: list[str] = Field(default_factory=list)
    dependency_restrictions: list[str] = Field(default_factory=list)
    discharge_target: str | None = None
    marker: str | None = None
    isolated: bool = False
    waiver_approver: str | None = None
    waiver_reason: str | None = None
    created_at: datetime = Field(default_factory=utc_now)
    updated_at: datetime = Field(default_factory=utc_now)

    @model_validator(mode="after")
    def marker_matches_taxonomy(self) -> "ProofObligation":
        expected = {
            ObligationKind.EXERCISE_DEFERRED: "EXERCISE-SORRY",
            ObligationKind.EXTERNAL_DEFERRED: "EXTERNAL-SORRY",
            ObligationKind.UNRESOLVED_PROOF: "UNRESOLVED-PROOF-",
            ObligationKind.FORWARD_DEPENDENCY: "FORWARD-SORRY-",
        }.get(self.kind)
        if expected and self.marker and expected not in self.marker:
            raise ValueError(f"marker for {self.kind} must contain {expected}")
        return self
