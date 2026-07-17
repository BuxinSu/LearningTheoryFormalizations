from __future__ import annotations

from pathlib import Path


def normalize_tex_tree(tex_root: Path) -> None:
    """Apply conservative encoding/newline normalization without rewriting TeX semantics."""
    for path in tex_root.rglob("*.tex"):
        text = path.read_text(encoding="utf-8", errors="replace")
        normalized = text.replace("\r\n", "\n").replace("\r", "\n")
        if not normalized.endswith("\n"):
            normalized += "\n"
        path.write_text(normalized, encoding="utf-8")

