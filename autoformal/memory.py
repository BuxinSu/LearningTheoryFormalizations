"""Compatibility facade for global theorem-memory persistence."""

from .adapters.persistence.knowledge_store import KnowledgeStore, normalize_lean_type

__all__ = ["KnowledgeStore", "normalize_lean_type"]
