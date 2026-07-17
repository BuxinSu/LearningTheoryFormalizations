"""Compatibility facade for operational state persistence.

New code should depend on application repository ports or import the concrete
adapter from ``autoformal.adapters.persistence`` only at the composition root.
"""

from .adapters.persistence.state_store import SCHEMA_VERSION, StateStore

__all__ = ["SCHEMA_VERSION", "StateStore"]
