"""Operational state, obligation, job, lease, and status commands."""

from typing import Annotated

import typer

from ...models import ObligationStatus
from ..context import config, emit, memory, state


def obligations(
    book_id: str,
    chapter: Annotated[str | None, typer.Option("--chapter")] = None,
) -> None:
    emit([item.model_dump(mode="json") for item in state().obligations(book_id, chapter)])


def waive_obligation(
    obligation_id: str,
    approver: Annotated[str, typer.Option("--approver")],
    reason: Annotated[str, typer.Option("--reason")],
) -> None:
    store = state()
    obligation = store.obligation(obligation_id)
    book = store.config(obligation.book_id)
    if not book.policy.allow_human_waivers:
        raise typer.BadParameter("active policy forbids obligation waivers")
    emit(
        store.transition_obligation(
            obligation_id, ObligationStatus.WAIVED, approver=approver, reason=reason
        )
    )


def jobs(book_id: str) -> None:
    emit([item.model_dump(mode="json") for item in state().jobs(book_id)])


def leases(book_id: str) -> None:
    emit([item.model_dump(mode="json") for item in state().leases(book_id)])


def status(book_id: str) -> None:
    store = state()
    value = store.status(book_id)
    for chapter in value["chapters"]:
        chapter["active_findings"] = store.active_findings(
            book_id, chapter["chapter_id"]
        )
        chapter["immediate_blockers"] = [
            item
            for item in chapter["active_findings"]
            if item.get("severity") == "blocker"
        ]
    value["memory_trust_levels"] = memory().trust_counts()
    emit(value)


def register(app: typer.Typer) -> None:
    app.command()(obligations)
    app.command("waive-obligation")(waive_obligation)
    app.command()(jobs)
    app.command()(leases)
    app.command()(status)
