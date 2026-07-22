"""Focused repository views for reusable theorem memory."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, TYPE_CHECKING

if TYPE_CHECKING:
    from .knowledge_store import KnowledgeStore


def _forward(name: str) -> Callable[..., Any]:
    def call(self, *args: Any, **kwargs: Any) -> Any:
        return getattr(self._store, name)(*args, **kwargs)

    call.__name__ = name
    return call


class RepositoryView:
    def __init__(self, store: "KnowledgeStore") -> None:
        self._store = store


class ReferenceRepository(RepositoryView):
    ingest = _forward("ingest_reference")
    put_blob = _forward("put_blob")
    verify_blobs = _forward("verify_blobs")


class DeclarationRepository(RepositoryView):
    ingest_module = _forward("ingest_lean_module")
    save = _forward("save_declaration")
    get = _forward("declaration")
    promote = _forward("promote")
    link_source = _forward("link_source_declaration")
    trust_counts = _forward("trust_counts")


class LiteratureRepository(RepositoryView):
    save_dossier = _forward("save_literature_dossier")
    record_strategy = _forward("record_proof_strategy")


class SearchRepository(RepositoryView):
    search = _forward("search")


@dataclass(frozen=True, slots=True)
class MemoryRepositories:
    references: ReferenceRepository
    declarations: DeclarationRepository
    literature: LiteratureRepository
    search: SearchRepository

    @classmethod
    def from_store(cls, store: "KnowledgeStore") -> "MemoryRepositories":
        return cls(
            references=ReferenceRepository(store),
            declarations=DeclarationRepository(store),
            literature=LiteratureRepository(store),
            search=SearchRepository(store),
        )
