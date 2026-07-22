from __future__ import annotations

from pathlib import Path

from ...agents.codex_cli import CodexCLI
from ...agents.prompt_renderer import PromptRenderer, verify_prompt_paths
from ...config import repository_root
from ...artifacts import ArtifactStore
from ...application.verification import VerificationRequest
from ...adapters.verification import verification_service
from ...infrastructure.git_worktree import GitWorkspace
from ...models import BookConfig, SourceManifest, Stage
from ...state import StateStore


def _required_reports(reports: Path, chapter_id: str) -> list[Path]:
    return [
        reports / f"Chapter{chapter_id}_inventory.json",
        reports / f"Chapter{chapter_id}_inventory.md",
        reports / f"Chapter{chapter_id}_dependency_map.md",
        reports / f"Chapter{chapter_id}_statement_audit.md",
        reports / f"Chapter{chapter_id}_proof_audit.md",
        reports / f"Chapter{chapter_id}_source_issues.md",
        reports / f"Chapter{chapter_id}_build_report.md",
    ]


def verify_draft_artifacts(
    config: BookConfig,
    state: StateStore,
    workspace: GitWorkspace,
    chapter_id: str,
    session_id: str | None = None,
) -> None:
    reports = workspace.path / "TranslationReport"
    missing_reports = [
        str(path) for path in _required_reports(reports, chapter_id) if not path.is_file()
    ]
    if missing_reports:
        state.set_chapter_stage(
            config.book_id, chapter_id, Stage.BLOCKED, draft_session_id=session_id
        )
        raise RuntimeError(
            "Codex omitted required chapter artifacts: " + ", ".join(missing_reports)
        )
    build_report = (reports / f"Chapter{chapter_id}_build_report.md").read_text(
        encoding="utf-8"
    )
    if "#print axioms" not in build_report:
        state.set_chapter_stage(
            config.book_id, chapter_id, Stage.BLOCKED, draft_session_id=session_id
        )
        raise RuntimeError("chapter build report does not document #print axioms checks")

    run = ArtifactStore(state.active_run_dir(config.book_id))
    active_job = state.active_job(config.book_id, chapter_id, {"formalizer"})
    verification = verification_service().verify(
        VerificationRequest(
            book_id=config.book_id,
            chapter_id=chapter_id,
            scan_root=workspace.path,
            report_prefixes=[f"reports/chapter-{chapter_id}"],
            commit_message=f"Draft chapter {chapter_id}",
            phase="draft",
            job_id=active_job.id if active_job else None,
            session_id=session_id,
        ),
        state,
        workspace,
        run,
    )
    if not verification.passed:
        state.set_chapter_stage(
            config.book_id, chapter_id, Stage.BLOCKED, draft_session_id=session_id
        )
        raise RuntimeError(f"Lean verification failed for chapter {chapter_id}")
    state.set_chapter_stage(
        config.book_id,
        chapter_id,
        Stage.DRAFTED,
        draft_session_id=session_id,
        latest_attempt_id=verification.attempt_id,
        last_green_attempt_id=verification.attempt_id,
    )
    state.set_book_stage(config.book_id, Stage.DRAFTED)


def draft_chapter(
    config: BookConfig,
    state: StateStore,
    renderer: PromptRenderer,
    workspace: GitWorkspace,
    chapter_id: str,
) -> None:
    manifest_path = state.active_run_dir(config.book_id) / "source" / "source-manifest.json"
    manifest = SourceManifest.model_validate_json(manifest_path.read_text(encoding="utf-8"))
    chapter = next((item for item in manifest.chapters if item.id == chapter_id), None)
    if not chapter:
        available = ", ".join(item.id for item in manifest.chapters)
        raise KeyError(f"chapter {chapter_id} not found; available: {available}")
    verify_prompt_paths([
        config.prompts.draft_template,
        config.prompts.formalization_policy,
        config.prompts.source_conventions,
        Path(manifest.canonical_tex_root),
        Path(chapter.tex_path),
        workspace.path,
    ])
    reports = workspace.path / "TranslationReport"
    reports.mkdir(parents=True, exist_ok=True)
    run = ArtifactStore(state.active_run_dir(config.book_id))
    prompt = renderer.render(config.prompts.draft_template, {
        "book_title": config.title,
        "book_id": config.book_id,
        "chapter_id": chapter_id,
        "pdf_path": config.input_pdf,
        "tex_root": manifest.canonical_tex_root,
        "chapter_tex_path": chapter.tex_path,
        "source_manifest_path": manifest_path,
        "lean_project_path": workspace.path,
        "lean_namespace": config.lean.namespace,
        "reports_dir": reports,
        "formalization_plan_path": run.path("plans/formalization-plan.json"),
        "memory_database": config.runtime_dir / "memory" / "knowledge.sqlite3",
        "allowed_paths": (state.active_job(config.book_id, chapter_id, {"formalizer"}).allowed_paths
                          if state.active_job(config.book_id, chapter_id, {"formalizer"}) else [str(workspace.path)]),
        "writable_root": workspace.path,
        "formalization_policy_path": config.prompts.formalization_policy,
        "source_conventions_path": config.prompts.source_conventions,
        "audit_schema_path": repository_root() / "schemas" / "audit_inventory.schema.json",
    })
    run.write_text(f"prompts/chapter-{chapter_id}-draft.md", prompt)
    chapter_state = state.chapter(config.book_id, chapter_id)
    state.set_chapter_stage(config.book_id, chapter_id, Stage.DRAFTING)
    state.set_book_stage(config.book_id, Stage.DRAFTING)
    result, session_id, command = CodexCLI(config.codex).run(
        prompt,
        workspace.path,
        repository_root() / "schemas" / "agent_result.schema.json",
        run.path(f"agent-events/chapter-{chapter_id}-draft.jsonl"),
        run.path(f"agent-events/chapter-{chapter_id}-draft-result.json"),
        model=config.codex.draft_model,
        session_id=chapter_state.get("draft_session_id"),
    )
    run.write_json(f"agent-events/chapter-{chapter_id}-draft-command.json", command)
    active_job = state.active_job(config.book_id, chapter_id, {"formalizer"})
    if session_id and active_job:
        state.save_agent_session(session_id, active_job.id, "codex_cli",
                                 {"phase": "draft", "status": result.status}, ended=result.status != "blocked")
    run.write_text(f"agent-events/chapter-{chapter_id}-draft.patch", workspace.diff())
    if result.status != "completed":
        state.set_chapter_stage(
            config.book_id, chapter_id, Stage.BLOCKED, draft_session_id=session_id
        )
        raise RuntimeError(f"Codex drafting did not complete: {result.summary}")
    verify_draft_artifacts(config, state, workspace, chapter_id, session_id)
