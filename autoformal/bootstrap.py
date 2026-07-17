"""Composition-root paths for the side-by-side AutoFormal implementation."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True, slots=True)
class AppPaths:
    """Repository-level paths supplied to application and adapter code."""

    repository: Path
    code: Path
    configs: Path
    profiles: Path
    prompts: Path
    schemas: Path
    runtime: Path
    output: Path

    @classmethod
    def from_repository(cls, repository: Path) -> "AppPaths":
        root = repository.resolve()
        return cls(
            repository=root,
            code=root / "code",
            configs=root / "configs",
            profiles=root / "profiles",
            prompts=root / "prompts",
            schemas=root / "schemas",
            runtime=root / ".autoformal",
            output=root / "output",
        )
