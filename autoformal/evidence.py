from __future__ import annotations

import hashlib
from pathlib import Path


def declaration_evidence_hashes(worktree: Path, declarations: list[str]) -> dict[str, str]:
    """Hash only files bearing the approved declarations, not the whole tree."""
    result: dict[str, str] = {}
    lean_files = [path for path in worktree.rglob("*.lean") if ".lake" not in path.parts]
    for declaration in declarations:
        matches = [path for path in lean_files if declaration in path.read_text(encoding="utf-8", errors="replace")]
        digest = hashlib.sha256()
        for path in sorted(matches):
            digest.update(path.relative_to(worktree).as_posix().encode()); digest.update(b"\0")
            digest.update(path.read_bytes()); digest.update(b"\0")
        result[declaration] = digest.hexdigest()
    return result
