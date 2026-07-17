from __future__ import annotations

import uuid

from ...agents.prompt_renderer import PromptRenderer
from ...infrastructure.git_worktree import GitWorkspace
from ...models import AgentJob, BookConfig, Stage
from ...state import StateStore
from ..job_control import LeaseSpec, managed_job
from ._correction_worker import revise_chapter
from .proofread import proofread_chapter


def correct_chapter(
    config: BookConfig,
    state: StateStore,
    renderer: PromptRenderer,
    workspace: GitWorkspace,
    chapter_id: str,
) -> list:
    runs = state.review_runs(config.book_id, chapter_id)
    if not runs:
        raise ValueError("proofread must run before correction")
    review_run = runs[0]
    validations = state.finding_validations(review_run.id)
    dispositions = {item.finding_id: item.disposition for item in validations}
    findings = state.active_findings(config.book_id, chapter_id)
    missing = [item["id"] for item in findings if item["id"] not in dispositions]
    if missing:
        raise ValueError(
            f"every finding must be independently validated before correction: {missing}"
        )
    actionable = {
        finding_id
        for finding_id, disposition in dispositions.items()
        if disposition in {"confirmed", "revised"}
    }
    job = AgentJob(
        id=f"job-{uuid.uuid4().hex}",
        book_id=config.book_id,
        chapter_id=chapter_id,
        role="corrector",
        pass_name="correction",
        input_snapshot_hash=review_run.semantic_fingerprint,
        allowed_paths=[
            str(workspace.path / config.lean.namespace / f"Chapter{chapter_id}"),
            str(workspace.path / "TranslationReport" / f"Chapter{chapter_id}"),
        ],
        status="running",
    )
    lease_specs = [
        LeaseSpec("chapter", job.allowed_paths[0]),
        LeaseSpec("report", job.allowed_paths[1]),
    ]
    with managed_job(
        state, job, lease_specs, config.codex.timeout_seconds
    ) as active_job:
        state.set_chapter_stage(config.book_id, chapter_id, Stage.CORRECTING)
        if actionable:
            chapter = state.chapter(config.book_id, chapter_id)
            completed = sum(
                item.role == "corrector"
                and item.chapter_id == chapter_id
                and item.status == "completed"
                for item in state.jobs(config.book_id)
            )
            cycle = completed + 1
            budget = int(
                chapter.get("pass_budgets", {}).get(
                    "correction", config.revision_limit
                )
            )
            if cycle > budget:
                raise RuntimeError(f"correction pass budget exhausted ({budget})")
            revised = {
                item.finding_id: item.revised_difference
                for item in validations
                if item.disposition == "revised" and item.revised_difference
            }
            revise_chapter(
                config,
                state,
                renderer,
                workspace,
                chapter_id,
                cycle,
                validated_finding_ids=actionable,
                revised_differences=revised,
            )
        result = proofread_chapter(
            config, state, renderer, workspace.path, chapter_id
        )
        active_job.status = "completed"
        active_job.checkpoint = state.review_runs(config.book_id, chapter_id)[0].id
        return result
