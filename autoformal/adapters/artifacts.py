from __future__ import annotations

import json
import os
import tempfile
from pathlib import Path
from typing import Any

from .system.hashing import sha256_file


def atomic_write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def atomic_write_json(path: Path, value: Any) -> None:
    if hasattr(value, "model_dump"):
        value = value.model_dump(mode="json")
    atomic_write_text(path, json.dumps(value, indent=2, sort_keys=True, default=str) + "\n")


class ArtifactStore:
    def __init__(self, run_dir: Path) -> None:
        self.run_dir = run_dir
        self.run_dir.mkdir(parents=True, exist_ok=True)

    def path(self, *parts: str) -> Path:
        path = self.run_dir.joinpath(*parts)
        path.parent.mkdir(parents=True, exist_ok=True)
        return path

    def write_json(self, relative: str, value: Any) -> Path:
        path = self.path(relative)
        atomic_write_json(path, value)
        return path

    def write_text(self, relative: str, value: str) -> Path:
        path = self.path(relative)
        atomic_write_text(path, value)
        return path

    def manifest(self) -> dict[str, str]:
        return {
            path.relative_to(self.run_dir).as_posix(): sha256_file(path)
            for path in sorted(self.run_dir.rglob("*"))
            if path.is_file() and path.name != "artifact-manifest.json"
        }

    def seal(self) -> Path:
        return self.write_json("artifact-manifest.json", self.manifest())

