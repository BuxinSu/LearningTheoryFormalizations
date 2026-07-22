from __future__ import annotations

from pathlib import Path

from ...evidence import declaration_evidence_hashes
from ...infrastructure.hashing import hash_tree, sha256_json
from ...models import BookConfig, HumanDecision
from ...state import StateStore
from .proofread import load_inventory


def decide_audit_unit(
    config: BookConfig,
    state: StateStore,
    worktree: Path,
    chapter_id: str,
    audit_unit_id: str,
    decision: str,
    approver: str,
    notes: str = "",
) -> HumanDecision:
    inventory = load_inventory(worktree, config.book_id, chapter_id)
    unit = next((item for item in inventory.units if item.id == audit_unit_id), None)
    if not unit:
        raise KeyError(f"unknown audit unit in chapter {chapter_id}: {audit_unit_id}")
    record = HumanDecision(
        audit_unit_id=audit_unit_id, decision=decision, approver=approver,
        source_hash=sha256_json(unit.model_dump(mode="json")),
        lean_hash=hash_tree(worktree), notes=notes,
        evidence_hashes=declaration_evidence_hashes(worktree, unit.lean_declarations),
    )
    state.save_decision(config.book_id, chapter_id, record)
    return record

