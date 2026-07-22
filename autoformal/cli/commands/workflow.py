"""Proofread and validated-correction commands."""

from typing import Annotated

import typer

from ...application.orchestrator import worktree_path
from ...application.services.correction import correct_chapter
from ...application.services.proofread import proofread_chapter
from ...lean.project import ensure_lean_project
from ..context import chapter_ids, config, emit, renderer, state


def proofread(
    book_id: str,
    chapter: Annotated[str | None, typer.Argument()] = None,
    whole_only: Annotated[bool, typer.Option("--whole-only")] = False,
) -> None:
    """Run immutable PDF/Lean statement, proof, axiom, and coverage audit."""
    book, store = config(book_id), state()
    results = {}
    for chapter_id in chapter_ids(book, store, chapter):
        results[chapter_id] = [
            item.model_dump(mode="json")
            for item in proofread_chapter(
                book,
                store,
                renderer(),
                worktree_path(book),
                chapter_id,
                whole_only=whole_only,
            )
        ]
    emit(results)


def correct(
    book_id: str,
    chapter: Annotated[str | None, typer.Argument()] = None,
) -> None:
    """Correct only validated findings, verify, and perform a fresh proofread."""
    book, store = config(book_id), state()
    workspace = ensure_lean_project(worktree_path(book), book.lean)
    results = {}
    for chapter_id in chapter_ids(book, store, chapter):
        results[chapter_id] = [
            item.model_dump(mode="json")
            for item in correct_chapter(
                book, store, renderer(), workspace, chapter_id
            )
        ]
    emit(results)


def register(app: typer.Typer) -> None:
    app.command()(proofread)
    app.command()(correct)
