from __future__ import annotations

from pathlib import Path

from ...adapters.verification import verification_service
from ...agents.codex_cli import CodexCLI
from ...agents.prompt_renderer import PromptRenderer
from ...application.verification import VerificationRequest
from ...artifacts import ArtifactStore
from ...config import repository_root
from ...infrastructure.git_worktree import GitWorkspace
from ...models import BookConfig, SourceManifest, Stage
from ...state import StateStore
from .proofread import inventory_path


def revise_chapter(
    config: BookConfig,
    state: StateStore,
    renderer: PromptRenderer,
    workspace: GitWorkspace,
    chapter_id: str,
    cycle: int,
    validated_finding_ids: set[str] | None = None,
    revised_differences: dict[str, str] | None = None,
) -> None:
    run = ArtifactStore(state.active_run_dir(config.book_id))
    manifest = SourceManifest.model_validate_json(
        run.path("source/source-manifest.json").read_text()
    )
    chapter = next(item for item in manifest.chapters if item.id == chapter_id)
    findings = state.active_findings(config.book_id, chapter_id)
    blocking = [
        finding
        for finding in findings
        if (
            validated_finding_ids is None and finding.get("severity") == "blocker"
        )
        or (
            validated_finding_ids is not None
            and finding.get("id") in validated_finding_ids
        )
    ]
    if revised_differences:
        blocking = [
            {**finding, "difference": revised_differences[finding["id"]]}
            if finding.get("id") in revised_differences
            else finding
            for finding in blocking
        ]
    if not blocking:
        return

    findings_path = run.write_json(
        f"reports/chapter-{chapter_id}-cycle-{cycle}-blocking-findings.json",
        blocking,
    )
    section_ids = sorted(
        {str(finding.get("audit_unit_id") or "chapter") for finding in blocking}
    )
    prompt = renderer.render(
        config.prompts.revision_template,
        {
            "book_title": config.title,
            "chapter_id": chapter_id,
            "section_id": ", ".join(section_ids),
            "pdf_path": config.input_pdf,
            "tex_path": chapter.tex_path,
            "inventory_path": inventory_path(workspace.path, chapter_id),
            "findings_path": findings_path,
            "lean_project_path": workspace.path,
            "writable_root": workspace.path,
        },
    )
    run.write_text(f"prompts/chapter-{chapter_id}-revision-{cycle}.md", prompt)
    chapter_state = state.chapter(config.book_id, chapter_id)
    completed_cycle = int(chapter_state.get("revision_cycle") or 0)
    state.set_chapter_stage(
        config.book_id, chapter_id, Stage.REVISING, revision_cycle=cycle
    )
    result, session_id, command = CodexCLI(config.codex).run(
        prompt,
        workspace.path,
        repository_root() / "schemas" / "agent_result.schema.json",
        run.path(f"agent-events/chapter-{chapter_id}-revision-{cycle}.jsonl"),
        run.path(f"agent-events/chapter-{chapter_id}-revision-{cycle}-result.json"),
        model=config.codex.revision_model,
        session_id=chapter_state.get("revision_session_id"),
    )
    run.write_json(
        f"agent-events/chapter-{chapter_id}-revision-{cycle}-command.json", command
    )
    active_job = state.active_job(
        config.book_id, chapter_id, {"corrector", "formalizer"}
    )
    if session_id and active_job:
        state.save_agent_session(
            session_id,
            active_job.id,
            "codex_cli",
            {"phase": "correction", "cycle": cycle, "status": result.status},
            ended=result.status != "blocked",
        )
    run.write_text(
        f"agent-events/chapter-{chapter_id}-revision-{cycle}.patch", workspace.diff()
    )
    if result.status == "failed":
        state.set_chapter_stage(
            config.book_id,
            chapter_id,
            Stage.BLOCKED,
            revision_session_id=session_id,
            revision_cycle=completed_cycle,
        )
        raise RuntimeError(f"Codex revision failed: {result.summary}")
    if result.status == "blocked":
        state.event(
            config.book_id,
            chapter_id,
            "partial_revision_checkpoint",
            {
                "cycle": cycle,
                "summary": result.summary,
                "unresolved_issues": result.unresolved_issues,
            },
        )

    verification = verification_service().verify(
        VerificationRequest(
            book_id=config.book_id,
            chapter_id=chapter_id,
            scan_root=workspace.path,
            report_prefixes=[
                f"reports/chapter-{chapter_id}-revision-{cycle}",
                f"reports/chapter-{chapter_id}",
            ],
            commit_message=f"Revise chapter {chapter_id}, cycle {cycle}",
            phase="correction",
            job_id=active_job.id if active_job else None,
            session_id=session_id,
            attempt_payload={"cycle": cycle},
        ),
        state,
        workspace,
        run,
    )
    if not verification.passed:
        state.set_chapter_stage(
            config.book_id,
            chapter_id,
            Stage.BLOCKED,
            revision_session_id=session_id,
            revision_cycle=completed_cycle,
        )
        raise RuntimeError(f"revision cycle {cycle} failed Lean verification")
    state.set_chapter_stage(
        config.book_id,
        chapter_id,
        Stage.DRAFTED,
        revision_session_id=session_id,
        revision_cycle=cycle,
        latest_attempt_id=verification.attempt_id,
        last_green_attempt_id=verification.attempt_id,
    )
