"""Stable serialized enums shared by AutoFormal domain models."""

from enum import StrEnum


class Stage(StrEnum):
    REGISTERED = "registered"
    PREFLIGHT = "preflight"
    PLANNED = "planned"
    FORMALIZING = "formalizing"
    PROOFREADING = "proofreading"
    CORRECTING = "correcting"
    REVIEW_CONDITIONAL = "review_conditional"
    SOURCE_READY = "source_ready"
    SOURCE_APPROVED = "source_approved"
    DRAFTING = "drafting"
    DRAFTED = "drafted"
    REVIEWING = "reviewing"
    REVISING = "revising"
    REVIEW_CLEAN = "review_clean"
    HUMAN_REVIEW = "human_review"
    FINALIZED = "finalized"
    BLOCKED = "blocked"
    FAILED = "failed"


class ObligationKind(StrEnum):
    EXERCISE_DEFERRED = "exercise_deferred"
    EXTERNAL_DEFERRED = "external_deferred"
    UNRESOLVED_PROOF = "unresolved_proof"
    FORWARD_DEPENDENCY = "forward_dependency"
    PROOF = "proof"
    SOURCE_ISSUE = "source_issue"
    HUMAN_REVIEW = "human_review"


class ObligationStatus(StrEnum):
    OPEN = "open"
    DISCHARGED = "discharged"
    WAIVED = "waived"
    REJECTED = "rejected"


class CoverageDecision(StrEnum):
    FORMALIZE = "formalize"
    DEFER = "defer"
    OMIT = "omit"
    SOURCE_ISSUE = "source_issue"


class CoverageStatus(StrEnum):
    FORMALIZED = "formalized"
    PARTIAL = "partial"
    MISSING = "missing"
    STRONGER = "stronger"
    UNSURE = "unsure"
    OUT_OF_SCOPE = "out_of_scope"
    COVERED_IN_APPENDIX = "covered_in_appendix"
    FORWARD_DEFERRED = "forward_deferred"
    JUSTIFIED_OMISSION = "justified_omission"
    SOURCE_ISSUE_RECORDED = "source_issue_recorded"


class TrustLevel(StrEnum):
    KERNEL_VERIFIED_CANDIDATE = "kernel_verified_candidate"
    REVIEWER_CLEAN = "reviewer_clean"
    HUMAN_APPROVED = "human_approved"
