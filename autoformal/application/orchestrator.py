from __future__ import annotations

import uuid
from pathlib import Path

from ..agents.prompt_renderer import PromptRenderer
from ..infrastructure.locking import file_lock
from ..lean.project import ensure_lean_project
from ..models import AgentJob, BookConfig, SourceManifest, Stage
from ..policy import resolve_policy_profile
from ..state import StateStore
from .job_control import LeaseSpec, managed_job
from .services.formalization import draft_chapter, verify_draft_artifacts
from .services.planning import plan_book
from .services.preflight import run_preflight
from .services.proofread import proofread_chapter


def worktree_path(config: BookConfig) -> Path:
    return config.runtime_dir / "worktrees" / config.book_id / "lean-project"


def renderer(root: Path) -> PromptRenderer:
    return PromptRenderer(root / "prompts")


def _check_chapter_known(
    config: BookConfig, state: StateStore, chapter_id: str
) -> None:
    manifest_path = (
        state.active_run_dir(config.book_id) / "source" / "source-manifest.json"
    )
    manifest = SourceManifest.model_validate_json(
        manifest_path.read_text(encoding="utf-8")
    )
    if chapter_id not in {chapter.id for chapter in manifest.chapters}:
        raise KeyError(f"unknown chapter: {chapter_id}")


def ensure_preflight_and_plan(
    config: BookConfig, state: StateStore, workspace: Path
) -> None:
    profile = state.active_policy_profile(config.book_id)
    expected = resolve_policy_profile(config)
    preflight = state.latest_preflight(config.book_id)
    if (
        not profile
        or profile.policy_hash != expected.policy_hash
        or not preflight
        or not preflight.passed
        or preflight.policy_hash != expected.policy_hash
    ):
        run_preflight(config, state, workspace)
    if not state.active_plan(config.book_id):
        plan_book(config, state, workspace)


def run_chapter_pipeline(
    root: Path,
    config: BookConfig,
    state: StateStore,
    chapter_id: str,
) -> None:
    book = state.book(config.book_id)
    allowed = {
        Stage.SOURCE_APPROVED,
        Stage.PREFLIGHT,
        Stage.PLANNED,
        Stage.FORMALIZING,
        Stage.DRAFTING,
        Stage.DRAFTED,
        Stage.PROOFREADING,
        Stage.CORRECTING,
        Stage.REVIEW_CONDITIONAL,
        Stage.REVIEW_CLEAN,
        Stage.HUMAN_REVIEW,
        Stage.BLOCKED,
        Stage.REVIEWING,
        Stage.REVISING,
    }
    if book["stage"] not in allowed:
        raise ValueError(
            f"source is not approved; current book stage is {book['stage']}"
        )
    workspace = ensure_lean_project(worktree_path(config), config.lean)
    ensure_preflight_and_plan(config, state, workspace.path)
    _check_chapter_known(config, state, chapter_id)
    prompt_renderer = renderer(root)
    lock_path = (
        config.runtime_dir / "locks" / f"{config.book_id}-chapter-{chapter_id}.lock"
    )
    with file_lock(lock_path):
        job = AgentJob(
            id=f"job-{uuid.uuid4().hex}",
            book_id=config.book_id,
            chapter_id=chapter_id,
            role="formalizer",
            pass_name="formalization",
            input_snapshot_hash=state.active_plan(config.book_id).id,
            allowed_paths=[
                str(
                    workspace.path
                    / config.lean.namespace
                    / f"Chapter{chapter_id}"
                ),
                str(
                    workspace.path
                    / "TranslationReport"
                    / f"Chapter{chapter_id}"
                ),
            ],
            status="running",
        )
        leases = [
            LeaseSpec("chapter", job.allowed_paths[0]),
            LeaseSpec("report", job.allowed_paths[1]),
        ]
        with managed_job(
            state, job, leases, config.codex.timeout_seconds
        ) as active_job:
            chapter_state = state.chapter(config.book_id, chapter_id)
            inventory = (
                workspace.path
                / "TranslationReport"
                / f"Chapter{chapter_id}_inventory.json"
            )
            ready = {
                Stage.DRAFTED,
                Stage.PROOFREADING,
                Stage.CORRECTING,
                Stage.REVIEW_CONDITIONAL,
                Stage.REVIEW_CLEAN,
            }
            if inventory.exists() and chapter_state["stage"] == Stage.BLOCKED:
                try:
                    verify_draft_artifacts(
                        config,
                        state,
                        workspace,
                        chapter_id,
                        chapter_state.get("draft_session_id"),
                    )
                except RuntimeError:
                    draft_chapter(
                        config, state, prompt_renderer, workspace, chapter_id
                    )
            elif chapter_state["stage"] not in ready or not inventory.exists():
                state.set_chapter_stage(
                    config.book_id, chapter_id, Stage.FORMALIZING
                )
                state.set_book_stage(config.book_id, Stage.FORMALIZING)
                draft_chapter(config, state, prompt_renderer, workspace, chapter_id)
            proofread_chapter(
                config, state, prompt_renderer, workspace.path, chapter_id
            )
            active_job.status = "completed"
            active_job.checkpoint = state.chapter(config.book_id, chapter_id).get(
                "last_green_attempt_id"
            )
