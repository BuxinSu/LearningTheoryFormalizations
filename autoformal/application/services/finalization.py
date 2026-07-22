from __future__ import annotations

import shutil
from datetime import datetime, timezone
from pathlib import Path

from ...artifacts import atomic_write_json
from ...evidence import declaration_evidence_hashes
from ...infrastructure.hashing import hash_tree, sha256_json
from ...lean.build import lake_build
from ...models import BookConfig, ChapterVerdict, SourceManifest, Stage
from ...state import StateStore
from .proofread import load_inventory


def finalize_chapter(
    config: BookConfig, state: StateStore, worktree: Path, chapter_id: str, approver: str
) -> Path:
    chapter_state = state.chapter(config.book_id, chapter_id)
    if chapter_state["stage"] != Stage.REVIEW_CLEAN:
        raise ValueError(f"chapter review is not clean; current stage is {chapter_state['stage']}")
    blockers = [finding for finding in state.active_findings(config.book_id, chapter_id) if finding["severity"] == "blocker"]
    if blockers:
        raise ValueError(f"chapter has {len(blockers)} active blocking findings")
    verdict_path = state.active_run_dir(config.book_id) / "reports" / f"chapter-{chapter_id}-verdict.json"
    if not verdict_path.is_file():
        raise ValueError("chapter verdict is missing")
    verdict = ChapterVerdict.model_validate_json(verdict_path.read_text(encoding="utf-8"))
    if not verdict.build_passed or verdict.blocking_findings or verdict.classification == "incomplete":
        raise ValueError(f"chapter verdict is not finalizable: {verdict.classification}")
    inventory = load_inventory(worktree, config.book_id, chapter_id)
    decisions = state.decisions(config.book_id, chapter_id)
    lean_hash = hash_tree(worktree)
    if verdict.artifact_hashes.get("lean_tree") != lean_hash:
        raise ValueError("chapter verdict is stale because the Lean tree changed after review")
    missing: list[str] = []
    stale: list[str] = []
    for unit in inventory.units:
        decision = decisions.get(unit.id)
        if not decision or decision.decision != "approved":
            missing.append(unit.id)
            continue
        evidence = declaration_evidence_hashes(worktree, unit.lean_declarations)
        lean_stale = (
            decision.evidence_hashes != evidence if decision.evidence_hashes
            else decision.lean_hash != lean_hash
        )
        if decision.source_hash != sha256_json(unit.model_dump(mode="json")) or lean_stale:
            stale.append(unit.id)
    if missing or stale:
        raise ValueError(f"human gate incomplete: missing={missing}, stale={stale}")
    open_obligations = [item for item in state.obligations(config.book_id, chapter_id)
                        if item.status.value == "open"]
    category_for_kind = {"exercise_deferred": "A", "external_deferred": "B"}
    forbidden = [item.id for item in open_obligations if item.kind.value not in category_for_kind]
    nonisolated = [item.id for item in open_obligations if item.kind.value in category_for_kind
                   and not item.isolated]
    disallowed = [item.id for item in open_obligations if item.kind.value in category_for_kind
                  and category_for_kind[item.kind.value] not in config.policy.allowed_gap_categories]
    if forbidden or nonisolated or disallowed:
        raise ValueError(
            f"chapter obligations prevent finalization: open={forbidden}, "
            f"nonisolated={nonisolated}, disallowed={disallowed}"
        )
    build = lake_build(worktree)
    if build.returncode != 0:
        raise ValueError("final Lean build failed")
    manifest = {
        "book_id": config.book_id, "chapter_id": chapter_id, "approver": approver,
        "finalized_at": datetime.now(timezone.utc).isoformat(), "lean_hash": lean_hash,
        "classification": verdict.classification,
        "chapter_verdict": verdict.model_dump(mode="json"),
        "build": build.model_dump(mode="json"),
        "decisions": [decision.model_dump(mode="json") for decision in decisions.values()],
    }
    destination = config.output_dir / config.book_id / f"Chapter{chapter_id}" / "final-manifest.json"
    atomic_write_json(destination, manifest)
    state.set_chapter_stage(config.book_id, chapter_id, Stage.FINALIZED)
    return destination


def finalize_book(config: BookConfig, state: StateStore, approver: str) -> Path:
    status = state.status(config.book_id)
    chapter_states = {chapter["chapter_id"]: chapter for chapter in status["chapters"]}
    source_manifest_path = state.active_run_dir(config.book_id) / "source" / "source-manifest.json"
    source_manifest = SourceManifest.model_validate_json(source_manifest_path.read_text(encoding="utf-8"))
    expected = [chapter.id for chapter in source_manifest.chapters]
    if not expected or any(
        chapter_id not in chapter_states or chapter_states[chapter_id]["stage"] != Stage.FINALIZED
        for chapter_id in expected
    ):
        raise ValueError("every discovered/formalized chapter must be finalized first")
    allowed_leaf_kinds = {"exercise_deferred", "external_deferred"}
    blocking_obligations = [item.id for item in state.obligations(config.book_id)
                            if item.status.value == "open" and (
                                item.kind.value not in allowed_leaf_kinds or not item.isolated
                            )]
    if blocking_obligations:
        raise ValueError(f"book has undischarged blocking obligations: {blocking_obligations}")
    manifest = {
        "book_id": config.book_id, "title": config.title, "approver": approver,
        "finalized_at": datetime.now(timezone.utc).isoformat(),
        "chapters": expected,
    }
    destination = config.output_dir / config.book_id / "final-manifest.json"
    atomic_write_json(destination, manifest)
    state.set_book_stage(config.book_id, Stage.FINALIZED)
    return destination

