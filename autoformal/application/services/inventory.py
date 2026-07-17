"""Canonical audit-inventory loading and legacy normalization."""

from __future__ import annotations

import json
import re
from pathlib import Path

from ...artifacts import atomic_write_json
from ...models import AuditInventory

def inventory_path(worktree: Path, chapter_id: str) -> Path:
    return worktree / "TranslationReport" / f"Chapter{chapter_id}_inventory.json"


def _legacy_inventory_to_contract(payload: dict, book_id: str, chapter_id: str) -> dict:
    items = payload.get("items")
    if not isinstance(items, list):
        raise ValueError("inventory does not match the contract and has no legacy items list")
    units: list[dict] = []
    for item in items:
        unit_id = str(item.get("id", ""))
        match = re.search(r"(\d+\.\d+)", unit_id)
        section_id = match.group(1) if match else chapter_id
        classification = str(item.get("correspondence_classification", ""))
        proof_status = str(item.get("proof_status", ""))
        location = str(item.get("source_location", ""))
        if "definition" in classification:
            kind = "definition"
        elif re.search(r"\(\d+\.\d+\.\d+\)|equation", location, re.IGNORECASE):
            kind = "numbered_equation"
        elif "named_result" in classification:
            kind = "named_result"
        else:
            kind = "prose_claim"
        lean_declarations = [str(value) for value in item.get("lean_declarations", [])]
        omitted = not lean_declarations and any(
            marker in classification
            for marker in ("unformalized", "not_formalizable", "scope_statement")
        )
        assumptions = item.get("assumptions", [])
        if isinstance(assumptions, str):
            assumptions = [assumptions] if assumptions else []
        units.append({
            "id": unit_id,
            "section_id": section_id,
            "kind": kind,
            "source_location": location,
            "claim": str(item.get("exact_claim", "")),
            "assumptions": [str(value) for value in assumptions],
            "decision": "omit" if omitted else "formalize",
            "omission_reason": (
                f"Codex classification: {classification}; proof status: {proof_status}"
                if omitted else None
            ),
            "lean_declarations": lean_declarations,
        })
    return {"book_id": book_id, "chapter_id": chapter_id, "units": units}


def _near_contract_inventory_to_contract(payload: dict) -> dict:
    """Normalize an agent-expanded inventory without discarding its coverage.

    Revision agents sometimes add useful, more specific ``kind`` labels than the
    stable interchange contract permits. The labels are taxonomy metadata, not
    semantic content, so collapse only unknown labels to their nearest contract
    kind and retain every unit, claim, decision, and declaration.
    """
    units = payload.get("units")
    if not isinstance(units, list):
        raise ValueError("inventory does not match the contract and has no units list")
    allowed = {
        "definition", "named_result", "numbered_equation", "display",
        "prose_claim", "negative_claim", "footnote", "hidden_obligation",
        "exercise", "example",
    }

    def normalize_kind(value: object) -> str:
        kind = str(value or "prose_claim")
        if kind in allowed:
            return kind
        if "definition" in kind:
            return "definition"
        if "equation" in kind:
            return "numbered_equation"
        if "named_result" in kind:
            return "named_result"
        if "exercise" in kind:
            return "exercise"
        if "example" in kind:
            return "example"
        if "negative" in kind:
            return "negative_claim"
        if "footnote" in kind:
            return "footnote"
        if "obligation" in kind:
            return "hidden_obligation"
        return "prose_claim"

    normalized = {
        "book_id": payload.get("book_id"),
        "chapter_id": payload.get("chapter_id"),
        "units": [],
    }
    for item in units:
        if not isinstance(item, dict):
            raise ValueError("inventory units must be JSON objects")
        unit = dict(item)
        unit["kind"] = normalize_kind(unit.get("kind"))
        normalized["units"].append(unit)
    return normalized


def load_inventory(worktree: Path, book_id: str, chapter_id: str) -> AuditInventory:
    path = inventory_path(worktree, chapter_id)
    if not path.is_file():
        raise FileNotFoundError(f"Codex did not produce required inventory: {path}")
    text = path.read_text(encoding="utf-8")
    try:
        inventory = AuditInventory.model_validate_json(text)
    except Exception:
        payload = json.loads(text)
        if isinstance(payload.get("units"), list):
            normalized = _near_contract_inventory_to_contract(payload)
        else:
            normalized = _legacy_inventory_to_contract(payload, book_id, chapter_id)
        raw_path = path.with_name(path.stem + ".raw.json")
        if not raw_path.exists():
            raw_path.write_text(text, encoding="utf-8")
        atomic_write_json(path, normalized)
        inventory = AuditInventory.model_validate(normalized)
    if inventory.book_id != book_id or inventory.chapter_id != chapter_id:
        raise ValueError(f"inventory identity mismatch: {path}")
    ids = [unit.id for unit in inventory.units]
    if len(ids) != len(set(ids)):
        raise ValueError(f"inventory contains duplicate audit IDs: {path}")
    return inventory


