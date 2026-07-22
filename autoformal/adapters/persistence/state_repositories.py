"""Focused repository views over the schema-v3 compatibility store.

The views provide bounded persistence surfaces while the compatibility
``StateStore`` methods remain available. Implementations can move out of the
facade one repository at a time without changing application services twice.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, TYPE_CHECKING

if TYPE_CHECKING:
    from .state_store import StateStore


def _forward(name: str) -> Callable[..., Any]:
    def call(self, *args: Any, **kwargs: Any) -> Any:
        return getattr(self._store, name)(*args, **kwargs)

    call.__name__ = name
    return call


class RepositoryView:
    def __init__(self, store: "StateStore") -> None:
        self._store = store


class BookRepository(RepositoryView):
    register = _forward("register_book")
    update_config = _forward("update_book_config")
    get = _forward("book")
    config = _forward("config")
    active_run_dir = _forward("active_run_dir")
    invalidate_chapters = _forward("invalidate_chapters")
    set_book_stage = _forward("set_book_stage")
    chapter = _forward("chapter")
    set_chapter_stage = _forward("set_chapter_stage")
    status = _forward("status")
    event = _forward("event")


class PlanningRepository(RepositoryView):
    save_policy_profile = _forward("save_policy_profile")
    active_policy_profile = _forward("active_policy_profile")
    save_preflight = _forward("save_preflight")
    latest_preflight = _forward("latest_preflight")
    save_plan = _forward("save_plan")
    active_plan = _forward("active_plan")
    save_source_claim = _forward("save_source_claim")
    source_claims = _forward("source_claims")


class ObligationRepository(RepositoryView):
    save = _forward("save_obligation")
    get = _forward("obligation")
    list = _forward("obligations")
    transition = _forward("transition_obligation")


class ExecutionRepository(RepositoryView):
    save_job = _forward("save_job")
    jobs = _forward("jobs")
    active_job = _forward("active_job")
    save_session = _forward("save_agent_session")
    acquire_lease = _forward("acquire_lease")
    release_lease = _forward("release_lease")
    leases = _forward("leases")
    create_attempt = _forward("create_attempt")


class ReviewRepository(RepositoryView):
    invalidate_findings = _forward("invalidate_review_findings")
    semantic_finding_key = _forward("semantic_finding_key")
    replace_findings = _forward("replace_findings")
    active_findings = _forward("active_findings")
    save_run = _forward("save_review_run")
    runs = _forward("review_runs")
    save_validation = _forward("save_finding_validation")
    validations = _forward("finding_validations")


class DecisionRepository(RepositoryView):
    save = _forward("save_decision")
    list = _forward("decisions")


@dataclass(frozen=True, slots=True)
class StateRepositories:
    books: BookRepository
    planning: PlanningRepository
    obligations: ObligationRepository
    execution: ExecutionRepository
    reviews: ReviewRepository
    decisions: DecisionRepository

    @classmethod
    def from_store(cls, store: "StateStore") -> "StateRepositories":
        return cls(
            books=BookRepository(store),
            planning=PlanningRepository(store),
            obligations=ObligationRepository(store),
            execution=ExecutionRepository(store),
            reviews=ReviewRepository(store),
            decisions=DecisionRepository(store),
        )
