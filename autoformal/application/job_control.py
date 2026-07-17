"""Exception-safe writer-job and path-lease lifecycle management."""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from typing import Iterator, Protocol

from ..models import AgentJob, PathLease


class JobState(Protocol):
    def save_job(self, job: AgentJob) -> None: ...
    def acquire_lease(
        self, book_id: str, job_id: str, scope: str, path: str, ttl_seconds: int
    ) -> PathLease: ...
    def release_lease(self, lease_id: str) -> None: ...


@dataclass(frozen=True, slots=True)
class LeaseSpec:
    scope: str
    path: str


@contextmanager
def managed_job(
    state: JobState,
    job: AgentJob,
    leases: list[LeaseSpec],
    ttl_seconds: int,
) -> Iterator[AgentJob]:
    """Persist a job and release every acquired lease on every exit path."""
    state.save_job(job)
    acquired: list[PathLease] = []
    try:
        for lease in leases:
            acquired.append(
                state.acquire_lease(
                    job.book_id, job.id, lease.scope, lease.path, ttl_seconds
                )
            )
        yield job
    except Exception:
        if job.status == "running":
            job.status = "failed"
        state.save_job(job)
        raise
    else:
        state.save_job(job)
    finally:
        for lease in reversed(acquired):
            state.release_lease(lease.id)
