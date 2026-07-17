"""CLI composition helpers; command modules contain no construction logic."""

from __future__ import annotations

import json
import os
from pathlib import Path

import typer

from ..agents.prompt_renderer import PromptRenderer
from ..config import repository_root
from ..memory import KnowledgeStore
from ..models import BookConfig, SourceManifest
from ..state import StateStore


def root() -> Path:
    override = os.environ.get("AUTOFORMAL_REPOSITORY_ROOT")
    return Path(override).resolve() if override else repository_root()


def state() -> StateStore:
    return StateStore(root() / ".autoformal" / "state.sqlite3")


def memory() -> KnowledgeStore:
    return KnowledgeStore(root() / ".autoformal" / "memory" / "knowledge.sqlite3")


def config(book_id: str) -> BookConfig:
    return state().config(book_id)


def renderer() -> PromptRenderer:
    return PromptRenderer(root() / "prompts")


def emit(value: object) -> None:
    if hasattr(value, "model_dump"):
        value = value.model_dump(mode="json")
    typer.echo(json.dumps(value, indent=2, default=str))


def chapter_ids(book: BookConfig, store: StateStore, chapter: str | None) -> list[str]:
    if chapter:
        return [chapter]
    path = store.active_run_dir(book.book_id) / "source" / "source-manifest.json"
    manifest = SourceManifest.model_validate_json(path.read_text(encoding="utf-8"))
    return [item.id for item in manifest.chapters]
