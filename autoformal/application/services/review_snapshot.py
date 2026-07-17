"""Immutable Lean-source snapshot construction for proofread jobs."""

from pathlib import Path

def lean_bundle(worktree: Path, namespace: str, chapter_id: str) -> str:
    chapter_root = worktree / namespace / f"Chapter{chapter_id}"
    candidates = set(chapter_root.rglob("*.lean")) if chapter_root.exists() else set()
    namespace_root = worktree / namespace
    candidates.update(namespace_root.glob(f"Chapter{chapter_id}_*.lean"))
    chapter_aggregator = namespace_root / f"Chapter{chapter_id}.lean"
    if chapter_aggregator.is_file():
        candidates.add(chapter_aggregator)
    if not candidates:
        candidates = {path for path in worktree.rglob("*.lean") if ".lake" not in path.parts}
    parts: list[str] = []
    for path in sorted(candidates):
        parts.append(f"\n===== LEAN {path.relative_to(worktree)} =====\n")
        parts.append(path.read_text(encoding="utf-8", errors="replace"))
    return "".join(parts)


