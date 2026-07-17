"""Book registration, source, preflight, planning, and chapter-run commands."""

from pathlib import Path
from typing import Annotated

import typer

from ...application.orchestrator import run_chapter_pipeline, worktree_path
from ...application.services.ingestion import approve_source, ingest_source
from ...application.services.planning import plan_book
from ...application.services.preflight import run_preflight
from ...artifacts import ArtifactStore
from ...config import load_book_config
from ...lean.project import ensure_lean_project
from ..context import config, emit, renderer, root, state


def init_book(
    config_path: Annotated[Path, typer.Argument(exists=True, dir_okay=False)],
) -> None:
    """Register a book, create its run, and scaffold a pinned Lean workspace."""
    repository = root()
    book = load_book_config(config_path, repository)
    expected_runtime = (repository / ".autoformal").resolve()
    if book.runtime_dir != expected_runtime:
        raise typer.BadParameter(f"runtime_dir must currently be {expected_runtime}")
    store = state()
    run_id = store.register_book(
        book, config_path.resolve(), book.runtime_dir / "runs"
    )
    ArtifactStore(book.runtime_dir / "runs" / run_id).write_text(
        "resolved-config.json", book.model_dump_json(indent=2) + "\n"
    )
    ensure_lean_project(worktree_path(book), book.lean)
    emit({"book_id": book.book_id, "run_id": run_id, "worktree": str(worktree_path(book))})


def refresh_book(
    config_path: Annotated[Path, typer.Argument(exists=True, dir_okay=False)],
) -> None:
    book = load_book_config(config_path, root())
    store = state()
    store.update_book_config(book, config_path.resolve())
    emit({"book_id": book.book_id, "reviewer_protocol": book.reviewer.protocol})


def ingest(book_id: str) -> None:
    book, store = config(book_id), state()
    emit(ingest_source(book, store, renderer()))


def approve_source_command(
    book_id: str,
    approver: Annotated[str, typer.Option("--approver")],
) -> None:
    emit(approve_source(config(book_id), state(), approver))


def preflight(book_id: str) -> None:
    """Run all hard source, policy, toolchain, build, and module checks."""
    book, store = config(book_id), state()
    workspace = ensure_lean_project(worktree_path(book), book.lean)
    emit(run_preflight(book, store, workspace.path))


def plan(book_id: str) -> None:
    """Discover claims and persist an acyclic formalization plan."""
    book, store = config(book_id), state()
    emit(plan_book(book, store, worktree_path(book)))


def run_chapter(book_id: str, chapter_id: str) -> None:
    """Preflight/plan, formalize, verify, then perform read-only proofread."""
    run_chapter_pipeline(root(), config(book_id), state(), chapter_id)
    emit(state().chapter(book_id, chapter_id))


def resume(book_id: str, chapter_id: str) -> None:
    run_chapter(book_id, chapter_id)


def register(app: typer.Typer) -> None:
    app.command("init-book")(init_book)
    app.command("refresh-book")(refresh_book)
    app.command()(ingest)
    app.command("approve-source")(approve_source_command)
    app.command()(preflight)
    app.command("plan-book")(plan)
    app.command("run-chapter")(run_chapter)
    app.command()(resume)
