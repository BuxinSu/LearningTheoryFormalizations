from __future__ import annotations

import hashlib
import json
import re
import uuid
from datetime import datetime, timezone
from pathlib import Path

from ...agents.codex_reviewer import CodexReviewer
from ...agents.prompt_renderer import PromptRenderer
from ...agents.reviewer_http import ReviewerHTTP
from ...artifacts import ArtifactStore, atomic_write_json
from ...contracts import verify_theorem_contracts
from ...config import repository_root
from ...infrastructure.hashing import hash_tree, sha256_file
from ...lean.axioms import print_axioms, public_declarations
from ...lean.dependencies import import_graph
from ...models import (
    AgentJob, AuditInventory, BookConfig, ChapterVerdict, ReviewerFinding, ReviewerResult,
    ReviewRun, SourceManifest, Stage,
)
from ...state import StateStore
from .inventory import (
    _legacy_inventory_to_contract,
    _near_contract_inventory_to_contract,
    inventory_path,
    load_inventory,
)
from .review_snapshot import lean_bundle
from .verdicts import chapter_verdict, classify_completion



def review_chapter(
    config: BookConfig,
    state: StateStore,
    renderer: PromptRenderer,
    worktree: Path,
    chapter_id: str,
    whole_only: bool = False,
) -> list[ReviewerFinding]:
    run = ArtifactStore(state.active_run_dir(config.book_id))
    proofread_job = AgentJob(
        id=f"job-{uuid.uuid4().hex}", book_id=config.book_id, chapter_id=chapter_id,
        role="proofreader", pass_name="proofread", read_only=True,
        input_snapshot_hash=hash_tree(worktree), allowed_paths=[str(worktree), str(config.input_pdf)],
        status="running",
    )
    state.save_job(proofread_job)
    manifest_path = run.path("source/source-manifest.json")
    manifest = SourceManifest.model_validate_json(manifest_path.read_text(encoding="utf-8"))
    chapter = next((item for item in manifest.chapters if item.id == chapter_id), None)
    if not chapter:
        raise KeyError(f"chapter not present in source manifest: {chapter_id}")
    inventory = load_inventory(worktree, config.book_id, chapter_id)
    lean_tree_before = hash_tree(worktree)
    lean_text = lean_bundle(worktree, config.lean.namespace, chapter_id)
    build_path = run.path(f"reports/chapter-{chapter_id}-build.json")
    placeholder_path = run.path(f"reports/chapter-{chapter_id}-placeholders.json")
    declarations = public_declarations(worktree)
    qualified_declarations = [
        name if "." in name else f"{config.lean.namespace}.{name}" for name in declarations
    ]
    axiom_result = print_axioms(
        worktree, sorted(import_graph(worktree)) or [config.lean.namespace], qualified_declarations,
        run.path(f"diagnostics/chapter-{chapter_id}-axioms"),
    ) if qualified_declarations else None
    if axiom_result is not None:
        run.write_json(f"reports/chapter-{chapter_id}-axioms.json", axiom_result)
    axiom_evidence = (
        axiom_result.stdout + "\n" + axiom_result.stderr if axiom_result is not None
        else "no public theorem declarations discovered"
    )
    chapter_reports: list[str] = []
    for report_path in sorted((worktree / "TranslationReport").glob(f"Chapter{chapter_id}_*.md")):
        chapter_reports.append(
            f"\n===== REPORT {report_path.name} =====\n"
            + report_path.read_text(encoding="utf-8", errors="replace")
        )
    schema_path = repository_root() / "schemas" / "reviewer_findings.schema.json"
    if config.reviewer.protocol == "codex_cli":
        reviewer: CodexReviewer | ReviewerHTTP = CodexReviewer(config.codex, config.reviewer, schema_path)
    else:
        reviewer = ReviewerHTTP(config.reviewer, schema_path, config.transport_retries)

    # Build timestamps change on every verification even when the checked
    # project is identical. Exclude them from reviewer evidence so successful
    # read-only audits remain resumable across retries.
    if build_path.exists():
        raw_build = json.loads(build_path.read_text(encoding="utf-8"))
        stable_build = {
            key: value for key, value in raw_build.items()
            if key not in {"started_at", "finished_at"}
        }
        build_evidence = json.dumps(stable_build, indent=2, sort_keys=True)
    else:
        build_evidence = "missing"

    input_manifest = {
        "source_manifest": sha256_file(manifest_path),
        "audit_inventory": sha256_file(inventory_path(worktree, chapter_id)),
        "lean_tree": lean_tree_before,
        "build": sha256_file(build_path) if build_path.exists() else "missing",
        "placeholders": sha256_file(placeholder_path) if placeholder_path.exists() else "missing",
        "axiom_declarations": hashlib.sha256("\n".join(qualified_declarations).encode()).hexdigest(),
    }
    semantic_fingerprint = hashlib.sha256(
        json.dumps(input_manifest, sort_keys=True).encode("utf-8")
    ).hexdigest()
    review_run = ReviewRun(
        id=f"review-{uuid.uuid4().hex}", book_id=config.book_id, chapter_id=chapter_id,
        input_manifest=input_manifest, semantic_fingerprint=semantic_fingerprint,
    )
    state.save_review_run(review_run)
    state.set_chapter_stage(config.book_id, chapter_id, Stage.PROOFREADING)
    state.set_book_stage(config.book_id, Stage.PROOFREADING)
    all_findings: list[ReviewerFinding] = []
    sections = [section.id for section in chapter.sections]
    if not sections:
        sections = sorted({unit.section_id for unit in inventory.units}) or [chapter_id]

    def run_review(section_id: str, whole_chapter: bool = False) -> ReviewerResult:
        units = inventory.units if whole_chapter else [
            unit for unit in inventory.units if unit.section_id == section_id
        ]
        section = next((item for item in chapter.sections if item.id == section_id), None)
        source_path = Path(chapter.tex_path if whole_chapter or section is None else section.tex_path)
        source_text = source_path.read_text(encoding="utf-8", errors="replace")
        label = "whole-chapter" if whole_chapter else f"section-{section_id.replace('.', '-')}"
        prompt = renderer.render(config.prompts.review_template, {
            "book_title": config.title,
            "chapter_id": chapter_id,
            "pdf_path": config.input_pdf,
            "section_id": "WHOLE_CHAPTER" if whole_chapter else section_id,
            "bundle_description": (
                f"{len(units)} audit units; source fragment {source_path}; "
                "Lean, build, placeholder, axiom, and audit-report evidence"
            ),
        })
        active_plan = state.active_plan(config.book_id)
        evidence = (
            f"\n\n===== ACTIVE POLICY PROFILE =====\n{config.prompts.formalization_policy.read_text(encoding='utf-8')}"
            f"\n\n===== APPROVED FORMALIZATION PLAN =====\n{json.dumps(active_plan.model_dump(mode='json') if active_plan else {}, indent=2)}"
            f"\n\n===== SOURCE FILE =====\n{source_path}"
            f"\n\n===== CANONICAL TEX FRAGMENT =====\n{source_text}"
            f"\n\n===== LEAN SOURCES =====\n{lean_text}"
            f"\n\n===== BUILD =====\n{build_evidence}"
            f"\n\n===== PLACEHOLDERS =====\n{placeholder_path.read_text() if placeholder_path.exists() else 'missing'}"
            f"\n\n===== #PRINT AXIOMS =====\n{axiom_evidence}"
            + "".join(chapter_reports)
        )
        prompt += "\n\n===== AUDIT INVENTORY =====\n" + json.dumps(
            {
                "book_id": config.book_id,
                "chapter_id": chapter_id,
                "units": [unit.model_dump(mode="json") for unit in units],
            },
            indent=2,
        ) + evidence
        prompt_rel = f"prompts/chapter-{chapter_id}-{label}-review.md"
        result_rel = f"agent-events/chapter-{chapter_id}-{label}-review-result.json"
        cache_rel = f"agent-events/chapter-{chapter_id}-{label}-review-prompt.sha256"
        prompt_hash = hashlib.sha256(prompt.encode("utf-8")).hexdigest()
        run.write_text(prompt_rel, prompt)
        run.write_text(f"reports/reviews/{review_run.id}/{label}-prompt.md", prompt)
        cached = False
        if isinstance(reviewer, CodexReviewer):
            cache_path = run.path(cache_rel)
            result_path = run.path(result_rel)
            if (
                cache_path.exists()
                and cache_path.read_text(encoding="utf-8").strip() == prompt_hash
                and result_path.exists()
            ):
                try:
                    result = ReviewerResult.model_validate_json(
                        result_path.read_text(encoding="utf-8")
                    )
                    cached = True
                except Exception:
                    cached = False
            if cached:
                state.event(
                    config.book_id, chapter_id, "codex_reviewer_cache_hit",
                    {"section": section_id, "whole_chapter": whole_chapter},
                )
            else:
                result, session_id, command = reviewer.review(
                    prompt,
                    worktree,
                    run.path(f"agent-events/chapter-{chapter_id}-{label}-review.jsonl"),
                    result_path,
                )
                run.write_json(
                    f"agent-events/chapter-{chapter_id}-{label}-review-command.json", command
                )
                run.write_text(cache_rel, prompt_hash + "\n")
                state.event(
                    config.book_id, chapter_id, "codex_reviewer_session",
                    {"section": section_id, "whole_chapter": whole_chapter, "session_id": session_id},
                )
        else:
            result = reviewer.review(prompt, attachments=[config.input_pdf])
        expected = {unit.id for unit in units}
        observed = {item.audit_unit_id for item in result.audit_results}
        for missing_id in sorted(expected - observed):
            result.findings.append(ReviewerFinding(
                id=f"AUTO-MISSING-AUDIT-{missing_id}", audit_unit_id=missing_id,
                severity="blocker", category="coverage_uncertain",
                source_location="audit inventory",
                difference="Reviewer returned no result for this audit unit.",
                evidence="The audit unit ID is absent from audit_results.",
                required_fix="Re-run a complete audit that explicitly classifies this unit.",
            ))
        if (
            result.assessment in {"substantially_complete_with_issues", "incomplete_or_inaccurate"}
            and not result.blockers
        ):
            result.findings.append(ReviewerFinding(
                id=f"AUTO-INCONSISTENT-ASSESSMENT-{label}", severity="blocker",
                category="coverage_uncertain", source_location="reviewer assessment",
                difference="Non-clean assessment has no blocking finding.",
                evidence=result.assessment,
                required_fix="Return actionable blocking findings or a clean assessment.",
            ))
        # Reviewer-local IDs such as F-001 are not globally unique. Namespace
        # them before aggregation so section findings cannot overwrite others.
        for finding in result.findings:
            if not finding.id.startswith(f"{label}:"):
                finding.id = f"{label}:{finding.id}"
        run.write_json(f"reports/chapter-{chapter_id}-{label}-review.json", result)
        run.write_text(f"reports/chapter-{chapter_id}-{label}-checker.md", result.markdown_report)
        run.write_json(f"reports/reviews/{review_run.id}/{label}-review.json", result)
        run.write_text(f"reports/reviews/{review_run.id}/{label}-checker.md", result.markdown_report)
        return result

    if not whole_only:
        for section_id in sections:
            result = run_review(section_id)
            all_findings.extend(result.findings)
    whole = run_review("WHOLE_CHAPTER", whole_chapter=True)
    all_findings.extend(whole.findings)
    plan = state.active_plan(config.book_id)
    chapter_contracts = [item for item in (plan.theorem_contracts if plan else [])
                         if item.chapter_id in {None, chapter_id}]
    contract_checks = verify_theorem_contracts(worktree, chapter_contracts)
    run.write_json(f"reports/chapter-{chapter_id}-contracts.json",
                   [item.model_dump(mode="json") for item in contract_checks])
    for check in contract_checks:
        if not check.passed:
            declaration = check.name.split(":", 1)[-1]
            all_findings.append(ReviewerFinding(
                id=f"AUTO-CONTRACT-{declaration}", severity="blocker",
                category="statement_mismatch", source_location="approved formalization plan",
                lean_location=declaration,
                difference="Required public theorem contract is missing, incompatible, or not genuinely proved.",
                evidence=check.details,
                required_fix="Restore the exact public signature and a genuine proof term.",
            ))
    if axiom_result is not None and axiom_result.returncode != 0:
        all_findings.append(ReviewerFinding(
            id="AUTO-AXIOM-CHECK-FAILED", severity="blocker", category="proof_gap",
            source_location="public declaration inventory", lean_location="axiom diagnostic",
            difference="#print axioms did not run successfully for every public result.",
            evidence=axiom_evidence[-4000:], required_fix="Repair imports/names and rerun the complete axiom audit.",
        ))
    elif "sorryAx" in axiom_evidence:
        open_registered = [item for item in state.obligations(config.book_id, chapter_id)
                           if item.status.value == "open"]
        permitted = bool(open_registered) and all(
            item.kind.value in {"unresolved_proof", "forward_dependency"}
            or (item.kind.value in {"exercise_deferred", "external_deferred"} and item.isolated)
            for item in open_registered
        )
        all_findings.append(ReviewerFinding(
            id="AUTO-TRANSITIVE-SORRYAX", severity="warning" if permitted else "blocker",
            category="proof_gap", source_location="public declaration inventory",
            lean_location="#print axioms output",
            difference="A public result transitively depends on Lean's sorryAx.",
            evidence=axiom_evidence[-4000:],
            required_fix=("Track conditional/deferred status until discharge."
                          if permitted else "Register, discharge, or isolate the proof gap."),
        ))

    findings = list({finding.id: finding for finding in all_findings}.values())
    if hash_tree(worktree) != lean_tree_before:
        raise RuntimeError("proofread pass modified Lean sources; reviewer snapshots are read-only")
    state.replace_findings(
        config.book_id, chapter_id, [finding.model_dump(mode="json") for finding in findings],
        review_run_id=review_run.id, origin="proofread",
    )
    blockers = [finding for finding in findings if finding.severity == "blocker"]
    placeholder_payload = json.loads(placeholder_path.read_text()) if placeholder_path.exists() else []
    open_obligations = [item for item in state.obligations(config.book_id, chapter_id)
                        if item.status.value == "open"]
    classification = classify_completion(len(blockers), open_obligations)
    build_payload = (
        json.loads(build_path.read_text())
        if build_path.exists()
        else {"returncode": 1}
    )
    verdict = chapter_verdict(
        book_id=config.book_id,
        chapter_id=chapter_id,
        classification=classification,
        build_passed=build_payload.get("returncode") == 0,
        blocker_count=len(blockers),
        audit_units=len(inventory.units),
        finding_count=len(findings),
        placeholder_count=len(placeholder_payload),
        theorem_contracts=len(contract_checks),
        contract_failures=sum(not item.passed for item in contract_checks),
        artifact_hashes={
            "source_manifest": sha256_file(manifest_path),
            "audit_inventory": sha256_file(inventory_path(worktree, chapter_id)),
            "lean_tree": hash_tree(worktree),
        },
    )
    run.write_json(f"reports/chapter-{chapter_id}-verdict.json", verdict)
    proofread_job.status = "completed"; proofread_job.checkpoint = review_run.id
    state.save_job(proofread_job)
    review_run.status = "complete"
    review_run.coverage_counts = verdict.counts
    review_run.completed_at = datetime.now(timezone.utc)
    state.save_review_run(review_run)
    run.write_json(f"reports/reviews/{review_run.id}/ledger.json", {
        "review_run": review_run.model_dump(mode="json"),
        "findings": [item.model_dump(mode="json") for item in findings],
        "verdict": verdict.model_dump(mode="json"),
    })
    if blockers or classification == "incomplete":
        state.set_chapter_stage(config.book_id, chapter_id, Stage.CORRECTING)
        state.set_book_stage(config.book_id, Stage.CORRECTING)
    elif classification == "structurally_complete_conditionally_verified":
        state.set_chapter_stage(config.book_id, chapter_id, Stage.REVIEW_CONDITIONAL)
        state.set_book_stage(config.book_id, Stage.REVIEW_CONDITIONAL)
    else:
        state.set_chapter_stage(config.book_id, chapter_id, Stage.REVIEW_CLEAN)
        state.set_book_stage(config.book_id, Stage.HUMAN_REVIEW)
    return findings


def proofread_chapter(config, state, renderer, worktree, chapter_id, whole_only=False):
    """Run an immutable statement/proof/coverage audit; never modify Lean."""
    return review_chapter(
        config, state, renderer, worktree, chapter_id, whole_only=whole_only
    )
