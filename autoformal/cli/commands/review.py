"""Finding validation, human decisions, and finalization commands."""

from __future__ import annotations

import json
import uuid
from typing import Annotated

import typer

from ...application.orchestrator import worktree_path
from ...application.services.finalization import finalize_book as finalize_book_service
from ...application.services.finalization import finalize_chapter as finalize_chapter_service
from ...application.services.human_review import decide_audit_unit
from ...models import FindingValidation
from ..context import config, emit, state


def validate_finding(
    book_id: str,
    chapter_id: str,
    finding_id: str,
    disposition: Annotated[str, typer.Option("--disposition")],
    validator: Annotated[str, typer.Option("--validator")],
    pdf_evidence: Annotated[str, typer.Option("--pdf-evidence")],
    lean_evidence: Annotated[str, typer.Option("--lean-evidence")],
    revised_difference: Annotated[
        str | None, typer.Option("--revised-difference")
    ] = None,
) -> None:
    """Record independent evidence before correction."""
    if disposition not in {"confirmed", "rejected", "revised"}:
        raise typer.BadParameter(
            "disposition must be confirmed, rejected, or revised"
        )
    store = state()
    runs = store.review_runs(book_id, chapter_id)
    if not runs:
        raise typer.BadParameter("no proofread run exists")
    finding_ids = {
        item["id"] for item in store.active_findings(book_id, chapter_id)
    }
    if finding_id not in finding_ids:
        raise typer.BadParameter(f"inactive or unknown finding: {finding_id}")
    validation = FindingValidation(
        id=f"validation-{uuid.uuid4().hex}",
        finding_id=finding_id,
        review_run_id=runs[0].id,
        disposition=disposition,
        pdf_evidence=pdf_evidence,
        lean_evidence=lean_evidence,
        revised_difference=revised_difference,
        validator=validator,
    )
    store.save_finding_validation(validation)
    emit(validation)


def _find_chapter(book, audit_unit_id: str, explicit: str | None) -> str:
    if explicit:
        return explicit
    matches = []
    reports = worktree_path(book) / "TranslationReport"
    for path in reports.glob("Chapter*_inventory.json"):
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        if any(unit.get("id") == audit_unit_id for unit in payload.get("units", [])):
            matches.append(str(payload.get("chapter_id")))
    if len(matches) != 1:
        raise typer.BadParameter(
            f"could not uniquely locate audit unit {audit_unit_id}; pass --chapter"
        )
    return matches[0]


def _decide(
    book_id: str,
    audit_unit_id: str,
    decision: str,
    approver: str,
    notes: str,
    chapter: str | None,
) -> None:
    book, store = config(book_id), state()
    chapter_id = _find_chapter(book, audit_unit_id, chapter)
    emit(
        decide_audit_unit(
            book,
            store,
            worktree_path(book),
            chapter_id,
            audit_unit_id,
            decision,
            approver,
            notes,
        )
    )


def approve_item(
    book_id: str,
    audit_unit_id: str,
    approver: Annotated[str, typer.Option("--approver")],
    notes: Annotated[str, typer.Option("--notes")] = "",
    chapter: Annotated[str | None, typer.Option("--chapter")] = None,
) -> None:
    _decide(book_id, audit_unit_id, "approved", approver, notes, chapter)


def reject_item(
    book_id: str,
    audit_unit_id: str,
    approver: Annotated[str, typer.Option("--approver")],
    notes: Annotated[str, typer.Option("--notes")],
    chapter: Annotated[str | None, typer.Option("--chapter")] = None,
) -> None:
    _decide(book_id, audit_unit_id, "rejected", approver, notes, chapter)


def finalize_chapter(
    book_id: str,
    chapter_id: str,
    approver: Annotated[str, typer.Option("--approver")],
) -> None:
    book = config(book_id)
    emit(
        {
            "final_manifest": str(
                finalize_chapter_service(
                    book, state(), worktree_path(book), chapter_id, approver
                )
            )
        }
    )


def finalize_book(
    book_id: str,
    approver: Annotated[str, typer.Option("--approver")],
) -> None:
    book = config(book_id)
    emit({"final_manifest": str(finalize_book_service(book, state(), approver))})


def register(app: typer.Typer) -> None:
    app.command("validate-finding")(validate_finding)
    app.command("approve-item")(approve_item)
    app.command("reject-item")(reject_item)
    app.command("finalize-chapter")(finalize_chapter)
    app.command("finalize-book")(finalize_book)
